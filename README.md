# Docker

The Dockerfile executes the main.py python file in order generate the state diagram (plantuml file) where it is then used to generate a .png file of the state diagram

To build the container's image
```
docker build -t prog_anal .
```

To run the container:
```
docker run -it --rm --volume $(pwd):/data --user $(id -u):$(id -g) prog_anal:latest -o <OUTPUT_FILE>

```

**When using the docker run, make sure that you are in the ProgramAnalysis_project dir, the OUTPUT_FILE overwrites any files with the same name**



In order to avoid having to do a docker build everytime something changes to the code, instead of doing a hard copy of the src dir to the container, the dir is instead mounted using docker volumes.


For development reasons,  instead of using the boilerplate code for argument parsing, all arguments are hard coded in the main.py file expect of the output file.



# Installation

No dependencies for application. 
For testing run: `pip install -U pytest`

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
Decompilation of a spicific `.class`-file can be done in one command:
```bash
docker run --rm -i kalhauge/jvm2json:latest jvm2json <Example.class > Example.json
```

All of these files needs to be stored in a single directory

## Setting up and running the interpreter
Setting up the interpreter requires a couple of 
```python
# Specify entry class and entry function
entry_class = utils.load_class("<PATH_TO_ENTRY_CLASS>.json")
entry_function = utils.load_method("<NAME_OF_ENTRY_FUNCTION>", entry_class)

# Specify state, e.g. args to entry function
state = [["entry_args"], [], 0, ("<NAME_OF_ENTRY_FUNCTION>", "<NAME_OF_ENTRY_CLASS>")]

# Initialize interpreter and set verbosity to True
intepreter = Interpreter(entry_function, True)

# Load rest of program into memory
program = utils.load_program("<PATH_CONTAINING_ALL_DECOMPILATED_JSON_FILES")
interpreter.load_program_into_memory(program)

# Run interpreter
interpreter.run(state)

# Get call trace after program termination
print(interpreter.call_trace)
```
