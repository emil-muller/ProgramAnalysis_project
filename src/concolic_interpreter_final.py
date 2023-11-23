from z3 import *
from concolic_types import Method, Bytecode
import datetime
import concolic_opcodes as co
import utils

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
        self.prog_returns = []
        self.call_trace = []
        self.param_dict_for_call_trace = {}
        self.call_traces = []
        self.param_dict_for_call_traces = []

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

    def load_program_into_memory(self, prog):
        for p in prog:
            class_name = p["name"]
            self.code_memory[class_name] = p

    def run(self, target: dict, step_limit: int, class_name: str, function_name: str):  # Tuple[Locals, OperStack, ProgramCounter, Invoker]):
        initial_method = self.current_method
        self.log_start()
        self.log_state()
        solver = Solver()
        print(target)
        # Handle param types here
        params = [Int(f"p{i}") for i, _ in enumerate(target["params"])]
        # params = [String(f"p{i}") for i, _ in enumerate(target["params"])]

        while solver.check() == sat:
            model = solver.model()
            self.call_trace = []
            self.param_dict_for_call_trace = {}
            self.current_method = initial_method
            # Add as_long for ints
            input = [model.eval(p, model_completion=True).as_long() for p in params]
            print(input)
            self.stack = [co.State(
                {k: co.ConcolicValue(i, p) for k, (i, p) in enumerate(zip(input, params))},
                [],
                0,
                (function_name, class_name, [])
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
            self.prog_returns.append(f"{input=} -> {self.program_return}")
            self.call_traces.append(self.call_trace)
            self.param_dict_for_call_traces.append(self.param_dict_for_call_trace)
        self.log_done()

    def step(self):
        if not self.stack:
            print("Couldn't step further")
            return False
        (l, s, pc, invoker) = self.stack[-1].unpack()
        #print(self.stack)
        #print(self.current_method)
        b = Bytecode(self.current_method["code"]["bytecode"][pc])
        if hasattr(self, f"op_{b.opr}"):
            return getattr(self, f"op_{b.opr}")(b)
        else:
            print(f"Couldn't find attr op_{b.opr}")
            return False

    def op_return(self, b):
        return co.op_return(self, b)

    def op_nop(self, b):
        return co.op_nop(self, b)

    def op_load(self, b):
        return co.op_load(self, b)

    def op_binary(self, b):
        return co.op_binary(self, b)

    def op_if(self, b):
        return co.op_if(self, b)

    def op_ifz(self, b):
        return co.op_ifz(self, b)

    def op_store(self, b):
        return co.op_store(self, b)

    def op_incr(self, b):
        return co.op_incr(self, b)

    def op_push(self, b):
        return co.op_push(self, b)

    def op_dup(self, b):
        return co.op_dup(self, b)

    def op_dup_x1(self, b):
        return co.op_dup_x1(self, b)

    def op_dup_x2(self, b):
        return co.op_dup_x2(self, b)

    def op_goto(self, b):
        return co.op_goto(self, b)

    def op_array_load(self, b):
        return co.op_array_load(self, b)

    def op_arraylength(self, b):
        return co.op_arraylength(self, b)

    def op_put(self, b):
        return co.op_put(self, b)

    def op_get(self, b):
        return co.op_get(self, b)

    def op_new(self, b):
        return co.op_new(self, b)

    def op_newarray(self, b):
        return co.op_newarray(self, b)

    def op_array_store(self, b):
        return co.op_array_store(self, b)

    def op_invoke(self, b):
        return co.op_invoke(self, b)

    def op_pop(self, b):
        return co.op_pop(self, b)

    def op_cast(self, b):
        return co.op_cast(self, b)


    def op_put(self, b):
        return co.op_put(self, b)


if __name__ == "__main__":
    entry_class_name = "classA"
    program_path = "../TestPrograms/CoreTests/out/production/CoreTests/"
    entry_class = utils.load_class(
        f"{program_path}{entry_class_name}.json")
    entry_function_name = "nestedIf"
    entry_function = utils.load_method(entry_function_name, entry_class, [])
    program = utils.load_program(program_path)

    test = ConcolicInterpreter(entry_function, False)
    test.load_program_into_memory(program)
    test.run(entry_function, 100000, entry_class_name, entry_function_name)

    print("\n\n".join(test.prog_returns))
    print()
    print(utils.final_sequence_diagram_concolic(test.call_traces, test.param_dict_for_call_traces,  test))
    print()
    print("\n\n".join(test.prog_returns))


