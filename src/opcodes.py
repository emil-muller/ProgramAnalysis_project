import utils
import uuid
import java_mock

LOCAL = 0
OPERANDSTACK = 1
PC = 2
INVOKEDBY = 3


def op_return(intepreter, b):
    # Note we should perhaps use the class pop function
    # but the slides contains errors, so I'm not sure
    print(f"op_return called on {b}")

    if len(intepreter.stack) == 1:
        (l, s, pc, invoker) = intepreter.stack.pop()
        if len(s) > 0:
            intepreter.program_return = s[-1]
        else:
            intepreter.program_return = None
    else:
        # Add return to calltrace
        intepreter.call_trace.append((intepreter.stack[-1][INVOKEDBY], intepreter.stack[-2][INVOKEDBY]))

        # pop stackframe and push function return value to previous stackframes operand stack
        (l, s, pc, invoker) = intepreter.stack.pop()
        if len(s) > 0:
            intepreter.stack[-1][OPERANDSTACK].append(s[-1])
        # Set program to invokee invoker and resume execution
        intepreter.program = utils.load_method(
            intepreter.stack[-1][INVOKEDBY][0],
            intepreter.code_memory[intepreter.stack[-1][INVOKEDBY][1]],
            intepreter.stack[-1][INVOKEDBY][2]
        )
    return b


def op_nop(interpreter, b):
    print(f"\n!!!!!op_nop called on {b}!!!!!\n")
    interpreter.stack[-1][PC] += 1
    return b


def op_load(interpreter, b):
    print(f"op_load called on {b}")
    v = interpreter.stack[-1][LOCAL][b["index"]]
    interpreter.stack[-1][OPERANDSTACK].append(v)
    interpreter.stack[-1][PC] += 1
    return b


def op_binary(interpreter, b):
    print(f"op_add called on {b}")

    # Grab last two values of stack
    v_2 = interpreter.stack[-1][OPERANDSTACK].pop()
    v_1 = interpreter.stack[-1][OPERANDSTACK].pop()

    if b["operant"] == "add":
        interpreter.stack[-1][OPERANDSTACK].append(
            v_1 + v_2
        )  # Add values and push the to stack
    elif b["operant"] == "mul":
        interpreter.stack[-1][OPERANDSTACK].append(
            v_1 * v_2
        )  # Multiply values and push the to stack
    elif b["operant"] == "sub":
        interpreter.stack[-1][OPERANDSTACK].append(
            v_1 - v_2
        )  # Subtract values and push the to stack
    elif b["operant"] == "div":
        interpreter.stack[-1][OPERANDSTACK].append(
            v_1 / v_2
        )  # Subtract values and push the to stack
    else:
        return interpreter.op_nop(b)
    interpreter.stack[-1][PC] += 1
    return b


def op_if(interpreter, b):
    print(f"op_if called on {b}")
    v_2 = interpreter.stack[-1][OPERANDSTACK].pop()
    v_1 = interpreter.stack[-1][OPERANDSTACK].pop()

    if b["condition"] == "gt":
        if v_1 < v_2:
            # Increase program counter if condition is met
            interpreter.stack[-1][PC] += 1
        else:
            # Jump to target if condition is not met
            interpreter.stack[-1][PC] = b["target"]
    if b["condition"] == "ge":
        if v_1 <= v_2:
            # Increase program counter if condition is met
            interpreter.stack[-1][PC] += 1
        else:
            # Jump to target if condition is not met
            interpreter.stack[-1][PC] = b["target"]
    if b["condition"] == "le":
        if v_1 > v_2:
            # Increase program counter if condition is met
            interpreter.stack[-1][PC] += 1
        else:
            # Jump to target if condition is not met
            interpreter.stack[-1][PC] = b["target"]
    return b


def op_ifz(interpreter, b):
    print(f"op_ifz called on {b}")
    v_1 = interpreter.stack[-1][OPERANDSTACK].pop()

    if b["condition"] == "le":
        if v_1 > 0:
            # Increase program counter if condition is met
            interpreter.stack[-1][PC] += 1
        else:
            # Jump to target if condition is not met
            interpreter.stack[-1][PC] = b["target"]
    if b["condition"] == "ne":
        if v_1 != 0:
            # Increase program counter if condition is met
            interpreter.stack[-1][PC] += 1
        else:
            # Jump to target if condition is not met
            interpreter.stack[-1][PC] = b["target"]
    return b


def op_store(interperter, b):
    print(f"op_store called on {b}")

    v_1 = interperter.stack[-1][OPERANDSTACK].pop()

    # Handle doubles
    if b["type"] == "double":
        try:
            interperter.stack[-1][LOCAL][b["index"]] = v_1
            interperter.stack[-1][LOCAL][b["index"] + 1] = v_1
        except IndexError:
            # If index not in locals, append variable
            # This might be dangerous if program assumes you can push
            # to arbitrary indexes
            interperter.stack[-1][LOCAL].append(v_1)
            interperter.stack[-1][LOCAL].append(v_1)
            interperter.stack[-1][PC] += 1
        return b

    # Handle integers and refs
    # Push value from stack to local variable at given index
    try:
        interperter.stack[-1][LOCAL][b["index"]] = v_1
    except IndexError:
        # If index not in locals, append variable
        # This might be dangerous if program assumes you can push
        # to arbitrary indexes
        interperter.stack[-1][LOCAL].append(v_1)
    interperter.stack[-1][PC] += 1
    return b


def op_incr(interpreter, b):
    print(f"op_incr called on {b}")
    try:
        interpreter.stack[-1][LOCAL][b["index"]] += b["amount"]
        interpreter.stack[-1][PC] += 1
    except IndexError:
        # If index not in locals we can't increment, so we run nop
        interpreter.op_nop(b)
    return b


def op_push(interpreter, b):
    print(f"op_push called on {b}")
    interpreter.stack[-1][OPERANDSTACK].append(b["value"]["value"])
    interpreter.stack[-1][PC] += 1
    return b


def op_dup(interpreter, b):
    print(f"op_dup called on {b}")
    v = interpreter.stack[-1][OPERANDSTACK][-1]
    interpreter.stack[-1][OPERANDSTACK].append(v)
    interpreter.stack[-1][PC] += 1
    return b


def op_goto(interpreter, b):
    # Note this only works for gotos within the routine
    # Currently we can't jump out of the function // assuming that's at all possible in jvm bytecode
    print(f"op_goto called on {b}")
    interpreter.stack[-1][PC] = b["target"]
    return b


def op_array_load(interpreter, b):
    print(f"op_array_load called on {b}")
    i = interpreter.stack[-1][OPERANDSTACK].pop()
    if i < 0:
        raise Exception("Tried to access negative array index")

    arr_ref = interpreter.stack[-1][OPERANDSTACK].pop()

    val = interpreter.memory[arr_ref][i]
    interpreter.stack[-1][OPERANDSTACK].append(val)
    interpreter.stack[-1][PC] += 1
    return b


def op_arraylength(interpreter, b):
    print(f"op_arraylength called on {b}")
    arr_ref = interpreter.stack[-1][OPERANDSTACK].pop()

    arr_len = len(interpreter.memory[arr_ref])
    interpreter.stack[-1][OPERANDSTACK].append(arr_len)
    interpreter.stack[-1][PC] += 1
    return b


def op_put(interpreter, b):
    print(f"op_put called on {b}")
    # Don't handle static puts
    if b["static"]:
        interpreter.op_nop(b)
        return b

    val = interpreter.stack[-1][OPERANDSTACK].pop()
    objref = interpreter.stack[-1][OPERANDSTACK].pop()
    name = b["field"]["name"]

    interpreter.memory[objref][name] = val
    interpreter.stack[-1][PC] += 1
    return b


def op_get(interpreter, b):
    print(f"op_get called on {b}")
    if b["static"]:
        interpreter.op_nop(b)
        return b

    objref = interpreter.stack[-1][OPERANDSTACK].pop()
    val = interpreter.memory[objref][b["field"]["name"]]
    interpreter.stack[-1][OPERANDSTACK].append(val)
    interpreter.stack[-1][PC] += 1
    return b


def op_new(interpreter, b):
    print(f"op_new called on {b}")
    class_name = f'{b["class"]}_{uuid.uuid4()}'

    interpreter.memory[class_name] = {}
    interpreter.stack[-1][OPERANDSTACK].append(class_name)
    interpreter.stack[-1][PC] += 1
    return b


def op_newarray(interpreter, b):
    print(f"op_newarray called on {b}")

    # Grab size of array
    size = interpreter.stack[-1][OPERANDSTACK].pop()

    # Create object reference and push to stack
    objref = f'Array_{uuid.uuid4()}'
    interpreter.stack[-1][OPERANDSTACK].append(objref)

    # Technically not necessary to initialize array in python
    # , but it makes the code more clear
    interpreter.memory[objref] = [0 for _ in range(size)]

    interpreter.stack[-1][PC] += 1
    return b


def op_array_store(interpreter, b):
    print(f"op_array_store called on {b}")
    val = interpreter.stack[-1][OPERANDSTACK].pop()
    index = interpreter.stack[-1][OPERANDSTACK].pop()
    arr_ref = interpreter.stack[-1][OPERANDSTACK].pop()

    interpreter.memory[arr_ref][index] = val

    interpreter.stack[-1][PC] += 1
    return b


def op_invoke(interpreter, b):
    print(f"op_invoke called on {b}")

    # Add objectref at "argument" to function
    if b["access"] in ["virtual", "interface", "special"]:
        n = 1
    else:
        n = 0

    n += len(b["method"]["args"])

    function_params = interpreter.stack[-1][OPERANDSTACK][-n:]
    interpreter.stack[-1][OPERANDSTACK] = interpreter.stack[-1][OPERANDSTACK][:-n]
    interpreter.stack[-1][PC] += 1

    new_stack_frame = [
        function_params,
        [],
        0,
        (b["method"]["name"], b["method"]["ref"]["name"], b["method"]["args"]),
    ]

    interpreter.stack.append(new_stack_frame)

    # Add call to calltrace
    interpreter.call_trace.append((interpreter.stack[-2][INVOKEDBY], interpreter.stack[-1][INVOKEDBY]))

    # God forgive me for this sin
    try:
        method = utils.load_method(
            b["method"]["name"], interpreter.code_memory[b["method"]["ref"]["name"]], b["method"]["args"]
        )
    except KeyError as e:
        print("Method not in memory, trying java mock")
        method = None
        if b["method"]["ref"]["name"].startswith("java/"):
            java_mock.system_call(interpreter, b)

    # If called method is found in interpreter memory, execute method
    # If not, pop stackframe and continue execution of current method,
    # with correct operand stack (assuming void function)
    if method:
        interpreter.program = method
    else:
        interpreter.stack.pop()

    return b
