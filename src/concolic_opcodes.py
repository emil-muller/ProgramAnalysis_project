from dataclasses import dataclass
from z3 import *

@dataclass(frozen = True)
class ConcolicValue:
    concrete: int | bool | str
    symbolic: ExprRef

    def __repr__(self):
        return f"{self.concrete} {self.symbolic}"

    @classmethod
    def from_const(cls, c):
        if isinstance(c, bool):
            return ConcolicValue(c, BoolVal(c))
        if isinstance(c, int):
            return ConcolicValue(c, IntVal(c))
        if isinstance(c, str):
            return ConcolicValue(c, StringVal(c))

        raise Exception(f"Unknown const")

    def binary(self, operant, other):
        DICT = {
            "sub": "__sub__",
            "add": "__add__",
        }
        if operant in DICT:
            opr = DICT[operant]
        else:
            if operant == "div":
                return ConcolicValue(
                    self.concrete // other.concrete,
                    self.symbolic / other.symbolic,
                )
            raise Exception("Unknown binary operation " + operant)

        return ConcolicValue(
            getattr(self.concrete, opr)(other.concrete),
            getattr(self.symbolic, opr)(other.symbolic)
        )

    def compare(self, copr, other):
        DICT = {
            "ne": "__ne__",
            "gt": "__gt__",
            "ge": "__ge__",
            "isnot": "__ne__",
        }
        if copr in DICT:
            opr = DICT[copr]
        else:
            raise Exception("Unknown comparison operation " + copr)

        return ConcolicValue(
            getattr(self.concrete, opr)(other.concrete),
            getattr(self.symbolic, opr)(other.symbolic)
        )

@dataclass
class State:
    local_variables: dict[int, ConcolicValue]
    stack: list[ConcolicValue]
    pc: int
    invokerenos: tuple[str, str]


    def unpack(self):
        return self.local_variables, self.stack, self.pc, self.invokerenos

    def push(self, value):
        self.stack.append(value)

    def pop(self):
        return self.stack.pop()

    def load(self, index):
        self.push(self.local_variables[index])

    def store(self, index):
        self.local_variables[index] = self.stack.pop()

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
        print("!!!!! Not Implemented !!!!!!")
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
    else:
        print("!!!!!! NO OPERATION MADE !!!!!!")
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

    # Handle return from functions here
    if b.type is None:
        interpreter.program_return = "Returned void"
    return b