import argparse
import os
import sys 

import utils
import bytecode_interpreter as inter

def run_interpreter(filename, method, package, classname):
    if os.path.exists(filename):
        entry_class = utils.load_class(filename)
    else:
        print ("File ",filename," does not exist!")
        sys.exit(1);

    entry_method = utils.load_method(method, entry_class)
    if os.path.exists(package):
        program = utils.load_program(package)
    else:
        print ("Package path ",filename," does not exist!")
        sys.exit(1);

    state = [["string_arg"],    # local variables 
             [],                # stackframes
             0,                 # program counter
             (method, classname)]   #(invoker_func,invoker_class)

    interpretation = inter.Interpreter(entry_method, True)
    interpretation.load_program_into_memory(program)

    interpretation.run(state)
    print(interpretation.program_return)
    
    return interpretation.call_trace


def generate_plantuml(call_trace, output_file):
    # Your logic to generate output based on provided arguments
    plantuml_output = utils.to_plantuml(call_trace)
    # Creating the output directory if it doesn't exist
    output_directory = os.path.dirname(output_file)
    if not os.path.exists(output_directory) and output_directory != "" :
        os.mkdir(output_directory)

    # Writing the output to the specified output file
    with open(output_file, 'w') as f:
        f.write(plantuml_output)

def main():
    parser = argparse.ArgumentParser(description="A java state diagram generator based on dynamic analysis")

   # # Adding command-line arguments
   # parser.add_argument('-f', '--file', required=True)
   # parser.add_argument('-m', '--method' , required=True)
   # parser.add_argument('-p', '--package', required=True)
   # parser.add_argument('-c', '--classname', required=True)
    parser.add_argument('-o', '--output', default='out')

    # Parsing the command-line arguments
    args = parser.parse_args()


    #Running interpreter
   # call_trace = run_interpreter(args.file, args.method, args.package, args.classname) 
    call_trace = run_interpreter("TestPrograms/static_calls/level1/Example.json","main", "TestPrograms/static_calls/level1/", "level1/Example")


    # Generating plantuml output file
    print("OUTPUT:", args.output);
    generate_plantuml(call_trace, args.output)

if __name__ == "__main__":
    main()



