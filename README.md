# Installation

Invoke a virtual environment:
```bash
virtualenv .env && . .env/bin/activate
```
Install dependencies:
```bash
pip install -r requirements.txt
```

# Test
All tests can be run with pytest like
`pytest`

# Running the interpreter
Running the interpreter is composed of 5 parts.

* Decompiling the java class files using `jvm2json`
* Loading the entry class
* Specifying an entry function
* Specifying an initial state
* Loading the rest of the program into memory
* Running the interpreter

## Decompilation
Decompilation of a specific `.class`-file can be done in one command:
```bash
docker run --rm -i kalhauge/jvm2json:latest jvm2json <Example.class > Example.json
```

All of these files needs to be stored in a single directory. We've provided a script that does this `TestPrograms/decompile.py`.

## Setting up and running the interpreter
The provided CLI tool has the following parameters:

| Short | Long | Description                                       |
|-------|----|---------------------------------------------------|
| -e    | --entry | The name of the entry function                    |
| -c    | --class | The name of the class of the entry function       |
| -p    | --program | The full path to the decompiled java byte code    |
| -k    |    | The maximum amount of opcodes processed every run |

Running the tool may look like this:
```bash
python main.py -c "Main" -p "/home/user/ProgramAnalysis_project/TestPrograms/ConcolicTests/out/production/ConcolicTests/" -e "CalculateSummary" -k 10000
```

Running the interpreter from code requires a couple of steps but can be setup like this:
```python
import utils
from concolic_interpreter import ConcolicInterpreter

# Define entry class name
entry_class_name = "Main"

# Specify path to decompilated jvm code
program_path = "../TestPrograms/ConcolicTests/out/production/ConcolicTests/"

# Load the decompiled entry class code from disk
entry_class = utils.load_class(
    f"{program_path}{entry_class_name}.json")

# Define the entry function name
entry_function_name = "CalculateSummary"

# Load the entry function from entry class code
entry_function = utils.load_method(entry_function_name, entry_class, [])

# Load the entire decompiled program from disk
program = utils.load_program(program_path)

# Invoke the interpreter with the entry function as an entry point (verbosity can be specified with the second parameter)
test = ConcolicInterpreter(entry_function, False)

# Load the entire program into interpreter memory
test.load_program_into_memory(program)

# Run the program
test.run(entry_function, 100000, entry_class_name, entry_function_name)

# Print the PlantUML code and considered path constraints
print("Considered constraints:")
print("\n".join(test.prog_returns))
print()
print("Final PlantUML code:")
print()
print(utils.final_sequence_diagram_concolic(test.call_traces, test.param_dict_for_call_traces,  test))
```