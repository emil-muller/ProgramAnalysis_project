from concolic_types import ConcolicValue

LOCAL = 0
OPERANDSTACK = 1
PC = 2
INVOKEDBY = 3


def system_call(interpreter, b):
    if interpreter.stack[-1][INVOKEDBY] == ('println', 'java/io/PrintStream', []) or interpreter.stack[-1][INVOKEDBY] == ('println', 'java/io/PrintStream', [{'kind': 'class', 'name': 'java/lang/String'}]):
        print(interpreter.stack[-1][LOCAL])
        # Add return to calltrace
        interpreter.call_trace.append((interpreter.stack[-1][INVOKEDBY], interpreter.stack[-2][INVOKEDBY], "return"))
        return

    if interpreter.stack[-1][INVOKEDBY] == ('<init>', 'java/lang/Object', []):
        print("Skipping java/lang/Object/<init>")
        interpreter.call_trace.append((interpreter.stack[-1][INVOKEDBY], interpreter.stack[-2][INVOKEDBY], "return"))
        return

    if interpreter.stack[-1][INVOKEDBY] == ('equals', 'java/lang/String', [{'kind': 'class', 'name': 'java/lang/Object'}]):
        val1 = interpreter.stack[-1][LOCAL].pop()
        val2 = interpreter.stack[-1][LOCAL].pop()
        interpreter.stack[-2][OPERANDSTACK].append(val1 == val2)
        interpreter.call_trace.append((interpreter.stack[-1][INVOKEDBY], interpreter.stack[-2][INVOKEDBY], "return"))
        return

    print(f"UNKNOWN SYSTEM COMMAND: {interpreter.stack[-1][INVOKEDBY]}\nEXITING...")
    quit()

def system_call_concolic(interpreter, b):
    if interpreter.stack[-1].invokerenos == ('println', 'java/io/PrintStream', []) or interpreter.stack[-1].invokerenos == ('println', 'java/io/PrintStream', [{'kind': 'class', 'name': 'java/lang/String'}]):
        print(interpreter.stack[-1].local_variables)
        # Add return to calltrace
        interpreter.call_trace.append((interpreter.stack[-1].invokerenos, interpreter.stack[-2].invokerenos, "return"))
        return

    if interpreter.stack[-1].invokerenos == ('<init>', 'java/lang/Object', []):
        print("Skipping java/lang/Object/<init>")
        interpreter.call_trace.append((interpreter.stack[-1].invokerenos, interpreter.stack[-2].invokerenos, "return"))
        return

    if interpreter.stack[-1].invokerenos == ('equals', 'java/lang/String', [{'kind': 'class', 'name': 'java/lang/Object'}]):
        val1 = interpreter.stack[-1].local_variables.pop()
        val2 = interpreter.stack[-1].local_variables.pop()
        interpreter.stack[-2].stack.append(ConcolicValue.from_const(val1 == val2))
        interpreter.call_trace.append((interpreter.stack[-1].invokerenos, interpreter.stack[-2].invokerenos, "return"))
        return
