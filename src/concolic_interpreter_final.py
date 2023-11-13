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

        # Handle param types here
        # params = [Int(f"p{i}") for i, _ in enumerate(target["params"])]
        params = [String(f"p{i}") for i, _ in enumerate(target["params"])]

        while solver.check() == sat:
            model = solver.model()

            # Add as_long for ints
            input = [model.eval(p, model_completion=True).as_string() for p in params]
            print(input)
            self.stack = [co.State(
                {k: co.ConcolicValue(i, p) for k, (i, p) in enumerate(zip(input, params))},
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
            print(f"{input=} -> {self.program_return}\n{z3.simplify(path_constraint)}")
            print()
            print()
            solver.add(Not(z3.simplify(path_constraint)))

        self.log_done()

    def step(self):
        if not self.stack:
            print("Couldn't step further")
            return False
        (l, s, pc, invoker) = self.stack[-1].unpack()
        # print(self.stack)
        b = Bytecode(self.current_method["code"]["bytecode"][pc])
        if hasattr(self, f"op_{b.opr}"):
            return getattr(self, f"op_{b.opr}")(b)
        else:
            print(f"Couldn't find attr op_{b.opr}")
            return False

    def op_get(self, b):
        return co.op_get(self, b)

    def op_ifz(self, b):
        return co.op_ifz(self, b)

    def op_load(self, b):
        return co.op_load(self, b)

    def op_push(self, b):
        return co.op_push(self, b)

    def op_if(self, b):
        return co.op_if(self, b)

    def op_new(self, b):
        return co.op_new(self, b)

    def op_store(self, b):
        return co.op_store(self, b)

    def op_binary(self, b):
        return co.op_binary(self, b)


    def op_incr(self, b):
        return co.op_incr(self, b)


    def op_goto(self, b):
        return co.op_goto(self, b)

    def op_return(self, b):
        return co.op_return(self, b)

if __name__ == "__main__":
    target = None

    with open("/tmp/Main.json", "r") as f:
        result = json.load(f)
        for m in result["methods"]:
            if m["name"] == "TestString":
                target = m
                break
    interpreter = ConcolicInterpreter(target, False)
    interpreter.run(1000)
