from datetime import datetime
import utils
import opcodes as op

LOCAL = 0
OPERANDSTACK = 1
PC = 2
INVOKEDBY = 3


class Interpreter:
    def __init__(self, p, verbose):
        self.program = p
        self.verbose = verbose
        self.memory = {}
        self.code_memory = {}
        self.stack = []
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

    def run(self, f):  # Tuple[Locals, OperStack, ProgramCounter, Invoker]):
        self.stack.append(f)
        self.log_start()
        self.log_state()
        while self.step():
            self.log_state()
            # continue
        self.log_done()

    def step(self):
        if not self.stack:
            print("Couldn't step further")
            return False
        print(self.stack[-1])
        (l, s, pc, invoker) = self.stack[-1]
        b = self.program["bytecode"][pc]
        if hasattr(self, f"op_{b['opr']}"):
            return getattr(self, f"op_{b['opr']}")(b)
        else:
            print(f"Couldn't find attr op_{b['opr']}")
            return False

    def load_program_into_memory(self, prog):
        for p in prog:
            class_name = p["name"]
            self.code_memory[class_name] = p

    def op_return(self, b):
        return op.op_return(self, b)

    def op_nop(self, b):
        return op.op_nop(self, b)

    def op_load(self, b):
        return op.op_load(self, b)

    def op_binary(self, b):
        return op.op_binary(self, b)

    def op_if(self, b):
        return op.op_if(self, b)

    def op_ifz(self, b):
        return op.op_ifz(self, b)

    def op_store(self, b):
        return op.op_store(self, b)

    def op_incr(self, b):
        return op.op_incr(self, b)

    def op_push(self, b):
        return op.op_push(self, b)

    def op_dup(self, b):
        return op.op_dup(self, b)

    def op_goto(self, b):
        return op.op_goto(self, b)

    def op_array_load(self, b):
        return op.op_array_load(self, b)

    def op_arraylength(self, b):
        return op.op_arraylength(self, b)

    def op_put(self, b):
        return op.op_put(self, b)

    def op_get(self, b):
        return op.op_get(self, b)

    def op_new(self, b):
        return op.op_new(self, b)

    def op_newarray(self, b):
        return op.op_newarray(self, b)

    def op_array_store(self, b):
        return op.op_array_store(self, b)

    def op_invoke(self, b):
        return op.op_invoke(self, b)

    def op_pop(self, b):
        return op.op_pop(self, b)


if __name__ == "__main__":
    entry_class = utils.load_class(
        "../TestPrograms/CoreTests/out/production/CoreTests/classA.json")
    entry_function = utils.load_method("nonOverlappingAlternatives", entry_class, [])
    program = utils.load_program(
        "../TestPrograms/CoreTests/out/production/CoreTests/")

    state = [[1], [], 0, (
        "nonOverlappingAlternatives", "classA", [])]  # local variables  # stackframes  # program counter # (invoker_func,invoker_class)
    test = Interpreter(entry_function, False)
    test.load_program_into_memory(program)

    test.run(state)
    uml_lst = utils.to_plantuml(test.call_trace, test)
    print('\n'.join(utils.compress_plantuml(uml_lst)))
