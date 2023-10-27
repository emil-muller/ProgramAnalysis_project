LOCAL = 0
OPERANDSTACK = 1
PC = 2
INVOKEDBY = 3

def system_call(interpreter, b):
    if interpreter.stack[-1][INVOKEDBY] == ('println','java/io/PrintStream'):
        print(interpreter.stack[-1][LOCAL])
        # Add return to calltrace
        interpreter.call_trace.append((interpreter.stack[-1][INVOKEDBY], interpreter.stack[-2][INVOKEDBY]))
    else:
        print(f"UNKNOWN SYSTEM COMMAND: {interpreter.stack[-1][INVOKEDBY]}\nEXITING...")
        quit()