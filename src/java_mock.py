LOCAL = 0
OPERANDSTACK = 1
PC = 2
INVOKEDBY = 3

def system_call(interpreter, b):
    if interpreter.stack[-1][INVOKEDBY] == ('println','java/io/PrintStream'):
        print(interpreter.stack[-1][LOCAL])