from dataclasses import dataclass
from z3 import *

@dataclass#(frozen = True)
class ConcolicValue:
    concrete: int | bool | str | float
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
        if isinstance(c, float):
            return ConcolicValue(c, RealVal(c))
        # Handle null values
        if not c:
            return ConcolicValue(c, BoolVal(False))

        raise Exception(f"Unknown const")

    def binary(self, operant, other):
        DICT = {
            "sub": "__sub__",
            "add": "__add__",
            "mul": "__mul__"
        }
        if operant in DICT:
            opr = DICT[operant]
            if opr == "__mul__":
                pass
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
            "le": "__le__",
            "lt": "__lt__",
            "eq": "__eq__",
            "isnot": "__ne__",
            "is": "__eq__",
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
    invokerenos: tuple[str, str, list]


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