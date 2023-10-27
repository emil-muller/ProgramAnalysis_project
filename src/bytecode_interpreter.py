from datetime import datetime
import utils
import java_mock

LOCAL = 0
OPERANDSTACK = 1
PC = 2
INVOKEDBY = 3


class Interpreter:
    def __init__(self, p, verbose):  # Program, verbose: bool):
        self.program = p
        self.verbose = verbose
        self.memory = {}
        self.stack = []
        self.program_return = None

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
                    # f.write(f"memory: \n{self.memory}\n")
                    f.write(
                        f"stack: \n\tlocals: {self.stack[-1][LOCAL]}\n\tstack: {self.stack[-1][OPERANDSTACK]}\n\trip: {self.stack[-1][PC]}\n"
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
            continue
        self.log_done()

    def step(self):
        if not self.stack:
            print("Couldn't step further")
            return False
        print(self.stack)
        (l, s, pc, invoker) = self.stack[-1]
        b = self.program["bytecode"][pc]
        if hasattr(self, f"op_{b['opr']}"):
            return getattr(self, f"op_{b['opr']}")(b)
        else:
            print(f"Couldn't find attr op_{b['opr']}")
            return False

    def load_program_into_memory(self, program):
        for p in program:
            class_name = p["name"]
            self.memory[class_name] = p

    def pop(self, b):
        (l, s, pc) = self.stack.pop()
        # Rule (pop_1)
        if b["words"] == 1:
            if len(s) < 1:
                return False
            self.stack.append((l, s[:-1], pc + 1))
        # Rule (pop_2)
        elif b["words"] == 2:
            if len(s) < 2:
                return False
            self.stack.append((l, s[:-2], pc + 1))
        else:
            return False

    def op_return(self, b):
        # Note we should perhaps use the class pop function
        # but the slides contains errors, so I'm not sure
        print(f"op_return called on {b}")
        if len(self.stack) == 1:
            (l, s, pc, invoker) = self.stack.pop()
            if len(s) > 0:
                self.program_return = s[-1]
            else:
                self.program_return = None
        else:
            (l, s, pc, invoker) = self.stack.pop()
            if len(s) > 0:
                self.stack[-1][OPERANDSTACK].append(s[-1])
            self.program = utils.load_method(self.stack[-1][INVOKEDBY][0], self.memory[self.stack[-1][INVOKEDBY][1]])
        return b

    def op_nop(self, b):
        print(f"\n!!!!!op_nop called on {b}!!!!!\n")
        self.stack[-1][PC] += 1
        return b

    def op_load(self, b):
        print(f"op_load called on {b}")
        #if b["type"] != "int" and b["type"] != "ref":
        #    return self.op_nop(b)
        v = self.stack[-1][LOCAL][b["index"]]
        self.stack[-1][OPERANDSTACK].append(v)
        self.stack[-1][PC] += 1
        return b

    def op_binary(self, b):
        print(f"op_add called on {b}")

        # We only care about ints
        #if b["type"] != "int":
        #    return self.op_nop(b)

        # Grab last two values of stack
        v_2 = self.stack[-1][OPERANDSTACK].pop()
        v_1 = self.stack[-1][OPERANDSTACK].pop()

        if b["operant"] == "add":
            self.stack[-1][OPERANDSTACK].append(
                v_1 + v_2
            )  # Add values and push the to stack
        elif b["operant"] == "mul":
            self.stack[-1][OPERANDSTACK].append(
                v_1 * v_2
            )  # Multiply values and push the to stack
        elif b["operant"] == "sub":
            self.stack[-1][OPERANDSTACK].append(
                v_1 - v_2
            )  # Subtract values and push the to stack
        elif b["operant"] == "div":
            self.stack[-1][OPERANDSTACK].append(
                v_1 / v_2
            )  # Subtract values and push the to stack
        else:
            return self.op_nop(b)
        self.stack[-1][PC] += 1
        return b

    def op_if(self, b):
        print(f"op_if called on {b}")
        v_2 = self.stack[-1][OPERANDSTACK].pop()
        v_1 = self.stack[-1][OPERANDSTACK].pop()

        if b["condition"] == "gt":
            if v_1 < v_2:
                # Increase program counter if condition is met
                self.stack[-1][PC] += 1
            else:
                # Jump to target if condition is not met
                self.stack[-1][PC] = b["target"]
        if b["condition"] == "ge":
            if v_1 <= v_2:
                # Increase program counter if condition is met
                self.stack[-1][PC] += 1
            else:
                # Jump to target if condition is not met
                self.stack[-1][PC] = b["target"]
        if b["condition"] == "le":
            if v_1 > v_2:
                # Increase program counter if condition is met
                self.stack[-1][PC] += 1
            else:
                # Jump to target if condition is not met
                self.stack[-1][PC] = b["target"]
        return b

    def op_ifz(self, b):
        print(f"op_ifz called on {b}")
        v_1 = self.stack[-1][OPERANDSTACK].pop()

        if b["condition"] == "le":
            if v_1 > 0:
                # Increase program counter if condition is met
                self.stack[-1][PC] += 1
            else:
                # Jump to target if condition is not met
                self.stack[-1][PC] = b["target"]
        if b["condition"] == "ne":
            if v_1 != 0:
                # Increase program counter if condition is met
                self.stack[-1][PC] += 1
            else:
                # Jump to target if condition is not met
                self.stack[-1][PC] = b["target"]
        return b

    def op_store(self, b):
        print(f"op_store called on {b}")

        #if b["type"] != "int" and b["type"] != "ref":
        #    return self.op_nop(b)

        v_1 = self.stack[-1][OPERANDSTACK].pop()

        if b["type"] == "double":
            try:
                self.stack[-1][LOCAL][b["index"]] = v_1
                self.stack[-1][LOCAL][b["index"]+1] = v_1
            except IndexError:
                # If index not in locals, append variable
                # This might be dangerous if program assumes you can push
                # to arbitrary indexes
                self.stack[-1][LOCAL].append(v_1)
                self.stack[-1][LOCAL].append(v_1)
                self.stack[-1][PC] += 1
            return b

        # Push value from stack to local variable at given index
        try:
            self.stack[-1][LOCAL][b["index"]] = v_1
        except IndexError:
            # If index not in locals, append variable
            # This might be dangerous if program assumes you can push
            # to arbitrary indexes
            self.stack[-1][LOCAL].append(v_1)
        self.stack[-1][PC] += 1
        return b

    def op_incr(self, b):
        print(f"op_incr called on {b}")
        try:
            self.stack[-1][LOCAL][b["index"]] += b["amount"]
            self.stack[-1][PC] += 1
        except IndexError:
            # If index not in locals we can't increment, so we run nop
            self.op_nop(b)
        return b

    def op_push(self, b):
        print(f"op_push called on {b}")
        # Only care about integers
        #if b["value"]["type"] != "integer":
        #    self.op_nop(b)
        #    return b
        self.stack[-1][OPERANDSTACK].append(b["value"]["value"])
        self.stack[-1][PC] += 1
        return b

    def op_dup(self, b):
        print(f"op_dup called on {b}")
        v = self.stack[-1][OPERANDSTACK][-1]
        self.stack[-1][OPERANDSTACK].append(v)
        self.stack[-1][PC] += 1
        return b

    def op_goto(self, b):
        print(f"op_goto called on {b}")
        self.stack[-1][PC] = b["target"]
        return b

    def op_array_load(self, b):
        print(f"op_array_load called on {b}")
        #if b["type"] != "int":
        #    self.op_nop(b)
        #    return b
        i = self.stack[-1][OPERANDSTACK].pop()
        if i < 0:
            raise Exception("Tried to access negative array index")

        arr_ref = self.stack[-1][OPERANDSTACK].pop()

        val = self.memory[arr_ref][i]
        self.stack[-1][OPERANDSTACK].append(val)
        self.stack[-1][PC] += 1
        return b

    def op_arraylength(self, b):
        print(f"op_arraylength called on {b}")
        arr_ref = self.stack[-1][OPERANDSTACK].pop()

        arr_len = len(self.memory[arr_ref])
        self.stack[-1][OPERANDSTACK].append(arr_len)
        self.stack[-1][PC] += 1
        return b

    def op_get(self, b):
        print(f"op_get called on {b}")
        # Only handle statics
        if not b["static"]:
            self.op_nop(b)
            return b

        class_name = b["field"]["class"]
        val_name = b["field"]["name"]

        # Don't load system classes
        # This will be handled by java_mock
        if class_name.startswith("java/"):
            self.op_nop(b)
            return b

        val = self.memory[class_name][val_name]
        self.stack[-1][OPERANDSTACK].append(val)

        self.stack[-1][PC] += 1
        return b

    def op_new(self, b):
        print(f"op_new called on {b}")
        class_name = b["class"]
        self.memory[class_name] = {}
        self.stack[-1][OPERANDSTACK].append(class_name)
        self.stack[-1][PC] += 1
        return b

    def op_newarray(self, b):
        print(f"op_newarray called on {b}")

        # Grab size of array
        size = self.stack[-1][OPERANDSTACK].pop()

        # Create object reference and push to stack
        self.stack[-1][OPERANDSTACK].append(len(self.memory) + 1)

        # Technically not necessary to initialize array in python
        # , but it makes the code more clear
        self.memory[self.stack[-1][OPERANDSTACK][-1]] = [0 for _ in range(size)]

        self.stack[-1][PC] += 1
        return b

    def op_array_store(self, b):
        print(f"op_array_store called on {b}")
        val = self.stack[-1][OPERANDSTACK].pop()
        index = self.stack[-1][OPERANDSTACK].pop()
        arr_ref = self.stack[-1][OPERANDSTACK].pop()

        self.memory[arr_ref][index] = val

        self.stack[-1][PC] += 1
        return b

    def op_invoke(self, b):
        print(f"op_invoke called on {b}")

        # We should also try to handle virtual access at some point
        #if b["access"] != "static":
        #    self.op_nop(b)
        #    return b

        n = len(b["method"]["args"])

        function_params = self.stack[-1][OPERANDSTACK][-n:]
        self.stack[-1][OPERANDSTACK] = self.stack[-1][OPERANDSTACK][:-n]
        self.stack[-1][PC] += 1

        new_stack_frame = [
            function_params,
            [],
            0,
            (b["method"]["name"], b["method"]["ref"]["name"]),
        ]
        self.stack.append(new_stack_frame)

        # God forgive me for this sin
        try:
            method = utils.load_method(
                b["method"]["name"], self.memory[b["method"]["ref"]["name"]]
            )
        except Exception as e:
            print("Method not in memory, trying java mock")
            method = None
            if b["method"]["ref"]["name"].startswith("java/"):
                java_mock.system_call(self, b)

        if method:
            self.program = method
        else:
            self.stack.pop()

        return b


if __name__ == "__main__":
    entry_class = utils.load_class("/home/user/Documents/Program_analysis/ProgramAnalysis_project/TestPrograms/static_calls/level1/Example.json")
    entry_function = utils.load_method("main", entry_class)
    program = utils.load_program("/home/user/Documents/Program_analysis/ProgramAnalysis_project/TestPrograms/static_calls/level1")


    state = [["string_arg"], [], 0, ("main","level1/Example")]  # local variables  # stackframes  # program counter # (invoker_func,invoker_class)
    test = Interpreter(entry_function, True)
    test.load_program_into_memory(program)
    test.run(state)
    print(test.program_return)
