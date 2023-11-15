from dataclasses import dataclass
from z3 import *
import utils
import java_mock
import uuid
from concolic_types import ConcolicValue, State

def op_ifz(interpreter, b):
    print(f"op_ifz called on {b}")
    v = interpreter.stack[-1].pop()
    if isinstance(v.concrete,str):
        z = ConcolicValue.from_const("")
    else:
        z = ConcolicValue.from_const(0)
    r = ConcolicValue.compare(z, b.condition, v)
    if r.concrete:
        interpreter.stack[-1].pc = b.target
        interpreter.path += [r.symbolic]
    else:
        interpreter.stack[-1].pc += 1
        interpreter.path += [Not(r.symbolic)]
    return b

def op_if(interpreter, b):
    print(f"op_if called on {b}")
    v2 = interpreter.stack[-1].pop()
    v1 = interpreter.stack[-1].pop()
    r = ConcolicValue.compare(v1, b.condition, v2)
    if r.concrete:
        interpreter.stack[-1].pc = b.target
        interpreter.path += [r.symbolic]
    else:
        interpreter.stack[-1].pc += 1
        interpreter.path += [Not(r.symbolic)]
    return b

def op_get(interpreter, b):
    print(f"op_get called on {b}")
    if b.field["name"] == "$assertionsDisabled":
        interpreter.stack[-1].push(ConcolicValue.from_const(False))
    else:
        objref = interpreter.stack[-1].stack.pop().concrete
        val = interpreter.memory[objref][b.field["name"]]
        interpreter.stack[-1].stack.append(val)
    interpreter.stack[-1].pc += 1
    return b

def op_load(interpreter, b):
    print(f"op_load called on {b}")
    interpreter.stack[-1].load(b.index)
    interpreter.stack[-1].pc += 1
    return b

def op_push(interpreter, b):
    print(f"op_push called on {b}")
    interpreter.stack[-1].push(ConcolicValue.from_const(b.value["value"]))
    interpreter.stack[-1].pc += 1
    return b

def op_new(interpreter, b):
    print(f"op_new called on {b}")
    if b.dictionary["class"] == "java/lang/AssertionError":
        interpreter.program_return = "AssertionError"
        return None  # Will terminate current execution

    class_name = f'{b.dictionary["class"]}_{uuid.uuid4()}'

    interpreter.memory[class_name] = {"class": b.dictionary["class"]}
    interpreter.stack[-1].stack.append(ConcolicValue.from_const(class_name))

    interpreter.stack[-1].pc += 1
    return b

def op_dup(interpreter, b):
    print(f"op_dup called on {b}")
    v = interpreter.stack[-1].stack[-1]
    interpreter.stack[-1].stack.append(v)
    interpreter.stack[-1].pc += 1
    return b

def op_store(interpreter, b):
    print(f"op_store called on {b}")
    interpreter.stack[-1].store(b.index)
    interpreter.stack[-1].pc += 1
    return b


def op_binary(interpreter, b):
    print(f"op_binary called on {b}")
    v2 = interpreter.stack[-1].pop()
    v1 = interpreter.stack[-1].pop()
    if b.operant == "div":
        if v2.concrete == 0:
            interpreter.program_return = "Divide by 0"
            interpreter.path += [v2.symbolic == 0]
            return None # Terminates program
        else:
            interpreter.path += [Not(v2.symbolic == 0)]
    r = v1.binary(b.operant, v2)
    interpreter.stack[-1].push(r)

    interpreter.stack[-1].pc += 1
    return b


def op_incr(interpreter, b):
    print(f"op_incr called on {b}")
    interpreter.stack[-1].load(b.index)
    v = interpreter.stack[-1].pop()
    interpreter.stack[-1].push(v.binary("add", ConcolicValue.from_const(b.amount)))
    interpreter.stack[-1].store(b.index)

    interpreter.stack[-1].pc += 1
    return b

def op_goto(interpreter, b):
    print(f"op_goto called on {b}")
    interpreter.stack[-1].pc = b.target
    return b

def op_return(interpreter, b):
    print(f"op_return called on {b}")
    if len(interpreter.stack) == 1:
        (l, s, pc, invoker) = interpreter.stack[-1].unpack()
        interpreter.stack.pop()
        if len(s) > 0:
            interpreter.program_return = ConcolicValue(s[-1].concrete, z3.simplify(s[-1].symbolic))
        else:
            interpreter.program_return = "Returned void"
    else:
        # Add return to calltrace
        interpreter.call_trace.append((interpreter.stack[-1].invokerenos, interpreter.stack[-2].invokerenos, "return"))

        # pop stackframe and push function return value to previous stackframes operand stack
        (l, s, pc, invoker) = interpreter.stack[-1].unpack()
        interpreter.stack.pop()
        if len(s) > 0:
            interpreter.stack[-1].stack.append(s[-1])
        # Set program to invokee invoker and resume execution
        interpreter.current_method = utils.load_method(
            interpreter.stack[-1].invokerenos[0],
            interpreter.code_memory[interpreter.stack[-1].invokerenos[1]],
            interpreter.stack[-1].invokerenos[2]
        )
    return b


def op_invoke(interpreter, b):
    print(f"op_invoke called on {b}")

    # Add objectref at "argument" to function
    if b.access in ["virtual", "interface", "special"]:
        n = 1
    else:
        n = 0

    n += len(b.method["args"])

    function_params = interpreter.stack[-1].stack[-n:]
    interpreter.stack[-1].stack = interpreter.stack[-1].stack[:-n]
    interpreter.stack[-1].pc += 1

    new_stack_frame = State(
        function_params,
        [],
        0,
        (b.method["name"], b.method["ref"]["name"], b.method["args"]),
    )

    interpreter.stack.append(new_stack_frame)

    # Add call to calltrace
    interpreter.call_trace.append((interpreter.stack[-2].invokerenos, interpreter.stack[-1].invokerenos, "invoke"))

    # God forgive me for this sin
    method = None
    if b.access == "static":
        method = utils.lookup_virtual_and_static_method(interpreter, b)

    if b.access == "virtual":
        method = utils.lookup_virtual_and_static_method(interpreter, b)

    if b.access == "special":
        method = utils.lookup_virtual_and_static_method(interpreter, b)

    # Handle interfaces
    # Danger, doesn't handle superclass recursion yet
    if b.access == "interface":
        objref = function_params[0]
        method = utils.lookup_interface_method(interpreter, b, objref)

    if not method:
        print("Method not in memory, trying java mock")
        if b.method["ref"]["name"].startswith("java/"):
            java_mock.system_call_concolic(interpreter, b)

    # If called method is found in interpreter memory, execute method
    # If not, pop stackframe and continue execution of current method,
    # with correct operand stack (assuming void function)
    if method:
        interpreter.current_method = method
    else:
        interpreter.stack.pop()

    return b


def op_put(interpreter, b):
    print(f"op_put called on {b}")
    # Don't handle static puts
    if b.static:
        interpreter.op_nop(b)
        return b

    val = interpreter.stack[-1].stack.pop()
    objref = interpreter.stack[-1].stack.pop().concrete
    name = b.field["name"]

    interpreter.memory[objref][name] = val
    interpreter.stack[-1].pc += 1
    return b