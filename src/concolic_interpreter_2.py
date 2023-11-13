import z3
from dataclasses import dataclass
import os
import json

target = None

filepath = os.path.abspath('../TestPrograms/simple/out/SymbolicExample.json')
print(filepath)

with open(filepath) as f:
    result = json.load(f)
    for m in result["methods"]:
        if m["name"] == "divideByTwo":
            target = m
            break

print(target)


@dataclass
class Bytecode:

    dictionary: dict

    def __getattr__(self, name):
        return self.dictionary[name]

    def __repr__(self):
        return f"{self.opr}" + ", ".join(
            f"{k}: {v}" for k, v in self.dictionary.items()
            if k != "opr" and k != "offset")


@dataclass(frozen=True)
class ConcolicValue:
    concrete: int | bool
    symbolic: z3.ExprRef

    def __repr__(self):
        return f"{self.concrete} {self.symbolic}"

    @classmethod
    def from_const(cls, c):
        if isinstance(c, bool):
            return ConcolicValue(c, z3.BoolVal(c))
        if isinstance(c, int):
            return ConcolicValue(c, z3.IntVal(c))

        raise Exception(f"Unknown const {c}")

    def binary(self, operant, other):
        DICT = {
            "sub": "__sub__",
            "add": "__add__",
        }
        if operant in DICT:
            opr = DICT[operant]
        else:
            if operant == "div":
                return ConcolicValue(
                    self.concrete // other.concrete,
                    self.symbolic / other.symbolic,
                )
            raise Exception("Unknown binary operation " + operant)

        return ConcolicValue(
            getattr(self.concrete, opr)(other.concrete),
            getattr(self.symbolic, opr)(other.symbolic)
        )

    def compare(self, copr, other):
        DICT = {
            "eq": "__eq__",
            "ne": "__ne__",
            "gt": "__gt__",
            "ge": "__ge__",
            "le": "__le__",
            "lt": "__lt__",
        }
        if copr in DICT:
            opr = DICT[copr]
        else:
            raise Exception("Unknown comparison operation " + copr)

        return ConcolicValue(
            getattr(self.concrete, opr)(other.concrete),
            getattr(self.symbolic, opr)(other.symbolic)
        )


@dataclass
class State:
    locals: dict[int, ConcolicValue]
    stack: list[ConcolicValue]

    def push(self, value):
        self.stack.append(value)

    def pop(self):
        if not self.stack:
            raise IndexError("pop from an empty stack")
            return
        return self.stack.pop()

    def load(self, index):
        self.push(self.locals[index])

    def store(self, index):
        self.locals[index] = self.stack.pop()


class ConcolicInterpreter:
    def __init__(self):
        self.state = State({}, {})
        self.bytecode = []
        self.path = []
        self.pc = 0
        # This list contains the information needed for the sequence diagram
        self.call_trace = []

    def concolic(self, target, k=1000):
        solver = z3.Solver()
        params = [z3.Int(f"param{i}") for i, _ in enumerate(target["params"])]
        print("----------")
        print(params)
        print("----------")

        self.bytecode = [Bytecode(b) for b in target["code"]["bytecode"]]

        while solver.check() == z3.sat:
            model = solver.model()
            input = [model.eval(p, model_completion=True).as_long()
                     for p in params]
            print(input)

            self.state = State(
                {k: ConcolicValue(i, p)
                 for k, (i, p) in enumerate(zip(input, params))},
                []
            )

            self.pc = 0
            # Path constraints
            self.path = []

            for _ in range(k):
                bc = self.bytecode[self.pc]
                self.pc += 1
                print("--------")
                print("State: ", self.state)
                print("Path: ", self.path)
                print(bc)
                print("--------")
                print("--------")

                if hasattr(self, f"op_{bc.opr}"):
                    result = getattr(self, f"op_{bc.opr}")(bc)
                    if result:
                        print("Return: ", result)
                        break
                else:
                    raise Exception(f"Unsupported bytecode: {bc}")
            else:
                result = "out of iterations"

            path_constraint = z3.And(self.path)
            print()
            print()
            print(input, " -> ", result, " PATH: ", path_constraint)
            print()
            print()
            solver.add(z3.Not(path_constraint))
            # break
    print("------------------------------------------------")

    def opr_get(self, bc):
        if bc.field["name"] == "$assertionsDisabled":
            self.state.push(ConcolicValue.from_const(False))

    def op_ifz(self, bc):
        v = self.state.pop()
        z = ConcolicValue.from_const(0)
        r = ConcolicValue.compare(z, bc.condition, v)
        if r.concrete:
            self.pc = bc.target
            self.path += [r.symbolic]
        else:
            self.path += [z3.Not(r.symbolic)]
        print("PC: ", self.pc)

    def of_if(self, bc):
        v2 = self.state.pop()
        v1 = self.state.pop()
        r = ConcolicValue.compare(v1, bc.condition, v2)
        if r.concrete:
            self.pc = bc.target
            self.path += [r.symbolic]
        else:
            self.path += [z3.Not(r.symbolic)]

    def op_new(self, bc):
        if bc.dictionary["class"] == "java/lang/AssertionError":
            result = "AssertionError"
            return result

    def op_load(self, bc):
        print("BC.INDEX: ", bc.index)
        self.state.load(bc.index)

    def op_store(self, bc):
        self.state.store(bc.index)

    def op_push(self, bc):
        self.state.push(
            ConcolicValue.from_const(bc.value["value"]))

    def op_binary(self, bc):
        print("STACK: ", self.state.stack)
        v2 = self.state.pop()
        print("STACK: ", self.state.stack)
        v1 = self.state.pop()
        if bc.operant == "div":
            if v2.concrete == 0:
                result = "Divide by 0"
                if "param" in str(v2.symbolic):
                    self.path += [v2.symbolic == 0]
                return result
            elif "param" in str(v2.symbolic):
                self.path += [z3.Not(v2.symbolic == 0)]
        r = v1.binary(bc.operant, v2)
        self.state.push(r)

    def op_incr(self, bc):
        self.state.load(bc.index)
        v1 = self.state.pop()
        self.state.push(
            v1.binary("add", ConcolicValue.from_const(bc.amount)))
        self.state.store(bc.index)

    def op_goto(self, bc):
        self.pc = bc.target

    def op_return(self, bc):
        if bc.type is None:
            result = "returned void"
        else:
            result = f"returned {self.state.pop()}"
        return result


concolic = ConcolicInterpreter()
concolic.concolic(target)
