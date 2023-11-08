LOCAL = 0
OPERANDSTACK = 1
PC = 2
INVOKEDBY = 3

def system_call(interpreter, b):
    if interpreter.stack[-1][INVOKEDBY] == ('println', 'java/io/PrintStream', []) or interpreter.stack[-1][INVOKEDBY] == ('println','java/io/PrintStream',[{'kind': 'class', 'name': 'java/lang/String'}]):
        print(interpreter.stack[-1][LOCAL])
        # Add return to calltrace
        interpreter.call_trace.append((interpreter.stack[-1][INVOKEDBY], interpreter.stack[-2][INVOKEDBY], "return"))
    elif interpreter.stack[-1][INVOKEDBY] == ('<init>', 'java/lang/Object',[]):
        print("Skipping java/lang/Object/<init>")
        interpreter.call_trace.append((interpreter.stack[-1][INVOKEDBY], interpreter.stack[-2][INVOKEDBY], "return"))
    else:
        print(f"UNKNOWN SYSTEM COMMAND: {interpreter.stack[-1][INVOKEDBY]}\nEXITING...")
        quit()