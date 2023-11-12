import z3
from dataclasses import dataclass
import os
import json

target = None

filepath = os.path.abspath('../TestPrograms/static_calls/level1/Example.json')
print(filepath)

with open(filepath) as f:
    result = json.load(f)
    for m in result["methods"]:
        if m["name"] == "main":
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


@dataclass(frozen = True)
class ConcolicValue:
    concrete: int | bool
    symbolic: ExprRef

    def __repr__(self):
        return f"{self.concrete} {self.symbolic}"

    @classmethod
    def from_const(cls, c):
        if isinstance(c, bool):
            return ConcolicValue(c, BoolVal(c))
        if isinstance(c, int):
            return ConcolicValue(c, IntVal(c))

        raise Exception(f"Unknown const")

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
            "ne": "__ne__",
            "gt": "__gt__",
            "ge": "__ge__",
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

    def pop(self, value):
        return self.stack.pop(value)

    def load(self, index):
        self.push(locals[index])

    def store(self, index):
        self.locals[index] = self.stack.pop()


class ConcolicInterpreter:
    def __init__(self, p, verbose):
        self.state = State()
        self.bytecode = []
        self.path = []
        self.pc = 0
        # This list contains the information needed for the sequence diagram
        self.call_trace = []

    def op_ifz(self, bc):
        v = self.state.pop()
        z = ConcolicValue.from_const(0)
        r = ConcolicValue.compare(z, bc.condition, v)
        if r.concrete:
            self.pc = bc.target
            self.path += [r.symbolic]
        else:
            self.path += [Not(r.symbolic)]
            self.pc += 1

    def concolic(self, target, k = 1000):
        solver = Solver()
        params = [Int(f"p{i}") for i, _ in enumerate(target["params"])]
        self.bytecode = [Bytecode(b) for b in target["code"]["bytecode"]]

        while solver.check() == sat:
            model = solver.model()
            input = [model.eval(p, model_completion=True).as_long() for p in params]
            print(input)

            state = State(
                {k: ConcolicValue(i, p) for k, (i, p) in enumerate(zip(input, params))},
                []
            )

            self.pc = 0
            #Path constraints
            self.path = []

            for _ in range(k):
                bc = self.bytecode[self.pc]
                pc += 1
                print("--------")
                print(state)
                print(path)
                print(bc)

                if hasattr(self, f"op_{bc.opr}"):
                    return getattr(self, f"op_{bc.opr}")(bc)
                elif bc.opr == "get" and bc.field["name"] == "$assertionsDisabled":
                    state.push(ConcolicValue.from_const(False))
                else:
                    raise Exception(f"Unsupported bytecode: {bc}")


                if bc.opr == "ifz":
                    v = state.pop()
                    z = ConcolicValue.from_const(0)
                    r = ConcolicValue.compare(z, bc.condition, v)
                    if r.concrete:
                        pc = bc.target
                        path += [r.symbolic]
                    else:
                        path += [Not(r.symbolic)]
                elif bc.opr == "if":
                    v2 = state.pop()
                    v1 = state.pop()
                    r = ConcolicValue.compare(v1, bc.condition, v2)
                    if r.concrete:
                        pc = bc.target
                        path += [r.symbolic]
                    else:
                        path += [Not(r.symbolic)]
                elif bc.opr == "new" and bc.dictionary["class"] == "java/lang/AssertionError":
                    result = "AssertionError"
                    break
                elif bc.opr == "load":
                    state.load(bc.index)
                elif bc.opr == "store":
                    state.store(bc.index)
                elif bc.opr == "push":
                    state.push(ConcolicValue.from_const(bc.value["value"]))
                elif bc.opr == "binary":
                    v2 = state.pop()
                    v1 = state.pop()
                    if bc.operant == "div":
                        if v2.concrete == 0:
                            result = "Divide by 0"
                            path += [v2.symbolic == 0]
                            break
                        else:
                            path += [Not(v2.symbolic == 0)]
                    r = v1.binary(bc.operant, v2)
                    state.push(r)
                elif bc.opr == "incr":
                    state.load(bc.index)
                    v = state.pop()
                    state.push(v1.binary("add", ConcolicValue.from_const(bc.amount)))
                    state.store(bc.index)
                elif bc.opr == "goto":
                    pc = bc.target
                elif bc.opr == "return":
                    if bc.type is None:
                        result = "returned void"
                    result = f"returned {state.pop()}"
                    break
                else:
                    raise Exception(f"Unsupported bytecode: {bc}")
            else:
                result = "out of iterations"

            path_constraint = And(*path)
            print()
            print()
            print(input, " -> ", result, path_constraint)
            print()
            print()
            solver.add(Not(path_constraint))
            break


concolic = ConcolicInterpreter()
concolic.concolic(target)
