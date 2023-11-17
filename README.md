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
state = [["entry_args"], [], 0, ("<NAME_OF_ENTRY_FUNCTION>", "<NAME_OF_ENTRY_CLASS>",["<ENTRY_FUCTION_PARAMS>,..."])]

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