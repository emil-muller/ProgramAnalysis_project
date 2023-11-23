import argparse
import utils
from concolic_interpreter import ConcolicInterpreter

argParser = argparse.ArgumentParser()
argParser.add_argument("-e", "--entry", help="The name of the entry function", required=True)
argParser.add_argument("-c", "--classname", help="The name of the class of the entry function", required=True)
argParser.add_argument("-p", "--program", help="The path to the decompiled java byte code", required=True)
argParser.add_argument("-k", help="The maximum amount of opcodes processed every run", required=True)
args = argParser.parse_args()

if __name__ == "__main__":
    entry_class_name = args.classname
    program_path = args.program
    entry_class = utils.load_class(
        f"{program_path}{entry_class_name}.json")
    entry_function_name = args.entry
    entry_function = utils.load_method(entry_function_name, entry_class, [])
    program = utils.load_program(program_path)

    test = ConcolicInterpreter(entry_function, False)
    test.load_program_into_memory(program)
    test.run(entry_function, int(args.k), entry_class_name, entry_function_name)

    print(utils.final_sequence_diagram(test.call_traces, test))