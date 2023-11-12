from dataclasses import dataclass
from z3 import *

@dataclass
class Bytecode:
    dictionary: dict

    def __getattr__(self, name):
        return self.dictionary[name]

    def __repr__(self):
        return f"{self.opr}" + ", ".join(
            f"{k}: {v}" for k, v in self.dictionary.items()
            if k != "opr" and k != "offset")

@dataclass
class Method:
    bytecode_lst: list[Bytecode]
    method_json: dict

@dataclass(frozen = True)
class ConcolicValue:
    concrete: int | bool
    symbolic: ExprRef

    def __repr__(self):
        return f"{self.concrete} {self.symbolic}"

    @classmethod
    def from_const(cls, c):
        if isinstance(c, bool):
            return ConcolicValue(c, BoolVal(c))
        if isinstance(c, int):
            return ConcolicValue(c, IntVal(c))

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
    z = ConcolicValue.from_const(0)
    r = ConcolicValue.compare(z, b.condition, v)
    if r.concrete:
        interpreter.stack[-1].pc = b.target
        interpreter.path += [r.symbolic]
    else:
        interpreter.path += [Not(r.symbolic)]
    interpreter.stack[-1].pc += 1
    return b

def op_get(interpreter, b):
    print(f"op_get called on {b}")
    if b.field["name"] == "$assertionsDisabled":
        interpreter.stack[-1].push(ConcolicValue.from_const(False))
    else:
        print("!!!!! Not Implemented !!!!!!")
    interpreter.stack[-1].pc += 1
    return b