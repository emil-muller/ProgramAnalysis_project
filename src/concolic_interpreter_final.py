from z3 import *
from dataclasses import dataclass
import json
import datetime
import concolic_opcodes as co

@dataclass
class Bytecode:
    dictionary: dict

    def __getattr__(self, name):
        return self.dictionary[name]

    def __repr__(self):
        return f"{self.opr}" + ", ".join(
            f"{k}: {v}" for k, v in self.dictionary.items()
            if k != "opr" and k != "offset")

@dataclass
class Method:
    bytecode_lst: list[Bytecode]
    method_json: dict

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
    local_variables: dict[int, ConcolicValue]
    stack: list[ConcolicValue]
    pc: int
    invokerenos: tuple[str, str]


    def unpack(self):
        return self.local_variables, self.stack, self.pc, self.invokerenos

    def push(self, value):
        self.stack.append(value)

    def pop(self):
        return self.stack.pop()

    def load(self, index):
        self.push(self.local_variables[index])

    def store(self, index):
        self.local_variables[index] = self.stack.pop()


class ConcolicInterpreter:
    def __init__(self, current_method: Method, verbose: bool):
        self.current_method = current_method
        self.verbose = verbose
        self.memory = {}
        self.code_memory = {}
        self.stack = []
        self.path = []
        self.program_return = None

        # This list contains the information needed for the sequence diagram
        self.call_trace = []

    def log_start(self):
        if self.verbose:
            with open("log/log.txt", "a") as f:
                f.write(f"----- Started logging for run {datetime.now()} -----\n")

    def log_state(self):
        if self.verbose:
            try:
                (l, s, pc, invoker) = self.stack[-1]
                b = self.program["bytecode"][pc]
                with open("log/log.txt", "a") as f:
                    f.write("----\n")
                    f.write(
                        f"stack: \n\t" +
                        f"locals: {self.stack[-1][LOCAL]}\n\t" +
                        f"operandstack: {self.stack[-1][OPERANDSTACK]}\n\t" +
                        f"rip: {self.stack[-1][PC]}\n"
                    )
                    f.write(f"bytecode: \n{b}\n")
                    f.write(f"stackframes:\n {self.stack}\n")
            except IndexError:
                print("No frames on stack")

    def log_done(self):
        if self.verbose:
            with open("log/log.txt", "a") as f:
                f.write(f"----- Ended logging for run {datetime.now()} -----\n\n")
    def run(self, step_limit: int):  # Tuple[Locals, OperStack, ProgramCounter, Invoker]):
        self.log_start()
        self.log_state()
        solver = Solver()

        params = [Int(f"p{i}") for i, _ in enumerate(target["params"])]

        while solver.check() == sat:
            model = solver.model()
            input = [model.eval(p, model_completion=True).as_long() for p in params]
            print(input)

            self.stack = [State(
                {k: ConcolicValue(i, p) for k, (i, p) in enumerate(zip(input, params))},
                [],
                0,
                ("invoker", "invokee")
            )]

            #Path constraints
            self.path = []

            # Execute bytecode
            k = 0
            while self.step() and k < step_limit:
                self.log_state()
                k += 1

            path_constraint = And(*self.path)
            print()
            print()
            print(f"{input=} -> {self.program_return}\n{path_constraint}")
            print()
            print()
            solver.add(Not(path_constraint))
            print(z3.simplify(path_constraint))

        self.log_done()

    def step(self):
        if not self.stack:
            print("Couldn't step further")
            return False
        (l, s, pc, invoker) = self.stack[-1].unpack()
        # Be aware python you actually have method_json :D
        b = Bytecode(self.current_method["code"]["bytecode"][pc])
        if hasattr(self, f"op_{b.opr}"):
            return getattr(self, f"op_{b.opr}")(b)
        else:
            print(f"Couldn't find attr op_{b.opr}")
            return False

    # Use for reference, delete when opcodes are implemented
    def concolic_run(self, target: Method, k = 1000):
        solver = Solver()
        params = [Int(f"p{i}") for i, _ in enumerate(target["params"])]
        self.bytecode = [Bytecode(b) for b in target["code"]["bytecode"]]

        while solver.check() == sat:
            model = solver.model()
            input = [model.eval(p, model_completion=True).as_long() for p in params]
            print(input)

            state = State(
                {k: ConcolicValue(i, p) for k, (i, p) in enumerate(zip(input, params))},
                [],
                0,
                ("invokee", "invoker")
            )

            pc = 0
            # Path constraints
            path = []

            for _ in range(k):
                bc = self.bytecode[pc]
                pc += 1
                print("--------")
                print(state)
                print(path)
                print(bc)

                if bc.opr == "get" and bc.field["name"] == "$assertionsDisabled":
                    state.push(ConcolicValue.from_const(False))
                elif bc.opr == "ifz":
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
            print(z3.simplify(path_constraint))
    def op_get(self, b):
        return co.op_get(self, b)

    def op_ifz(self, b):
        return co.op_ifz(self, b)

if __name__ == "__main__":
    target = None

    with open("/tmp/Arithmetics.json", "r") as f:
        result = json.load(f)
        for m in result["methods"]:
            if m["name"] == "itDependsOnLattice3":
                target = m
                break
    interpreter = ConcolicInterpreter(target, False)
    # interpreter.concolic_run(target)
    interpreter.run(10)
