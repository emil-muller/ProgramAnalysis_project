import random
import pytest
import utils
from bytecode_interpreter import Interpreter


def test_zero():
    program = {
        "max_stack": 1,
        "max_locals": 0,
        "exceptions": [],
        "stack_map": None,
        "bytecode": [
            {"offset": 0, "opr": "push", "value": {"type": "integer", "value": 0}},
            {"offset": 1, "opr": "return", "type": "int"},
        ],
    }
    interpreter = Interpreter(program, False)

    interpreter.run([[1, 2, 3, 4], [1, 2, 3, 4], 0, None])
    assert interpreter.program_return == 0


def test_hundredAndTwo():
    program = {
        "max_stack": 1,
        "max_locals": 0,
        "exceptions": [],
        "stack_map": None,
        "bytecode": [
            {"offset": 0, "opr": "push", "value": {"type": "integer", "value": 102}},
            {"offset": 2, "opr": "return", "type": "int"},
        ],
    }
    interpreter = Interpreter(program, False)

    interpreter.run([[1, 2, 3, 4], [1, 2, 3, 4], 0, None])
    assert interpreter.program_return == 102


def test_identity():
    program = {
        "max_stack": 1,
        "max_locals": 1,
        "exceptions": [],
        "stack_map": None,
        "bytecode": [
            {"offset": 0, "opr": "load", "type": "int", "index": 0},
            {"offset": 1, "opr": "return", "type": "int"},
        ],
    }
    interpreter = Interpreter(program, False)

    interpreter.run([[420], [1, 2, 3, 4], 0, None])
    assert interpreter.program_return == 420


def test_add():
    program = {
        "max_stack": 2,
        "max_locals": 2,
        "exceptions": [],
        "stack_map": None,
        "bytecode": [
            {"offset": 0, "opr": "load", "type": "int", "index": 0},
            {"offset": 1, "opr": "load", "type": "int", "index": 1},
            {"offset": 2, "opr": "binary", "type": "int", "operant": "add"},
            {"offset": 3, "opr": "return", "type": "int"},
        ],
    }
    interpreter = Interpreter(program, False)

    interpreter.run([[420, 69], [1, 2, 3, 4], 0, None])
    assert interpreter.program_return == 489


def test_min():
    program = {
        "max_stack": 2,
        "max_locals": 2,
        "exceptions": [],
        "stack_map": [{"index": 5, "type": "same"}],
        "bytecode": [
            {"offset": 0, "opr": "load", "type": "int", "index": 0},
            {"offset": 1, "opr": "load", "type": "int", "index": 1},
            {"offset": 2, "opr": "if", "condition": "gt", "target": 5},
            {"offset": 5, "opr": "load", "type": "int", "index": 0},
            {"offset": 6, "opr": "return", "type": "int"},
            {"offset": 7, "opr": "load", "type": "int", "index": 1},
            {"offset": 8, "opr": "return", "type": "int"},
        ],
    }
    interpreter = Interpreter(program, False)

    interpreter.run([[420, 69], [], 0, None])
    assert interpreter.program_return == 69

    interpreter.run([[2, 69], [], 0, None])
    assert interpreter.program_return == 2


def test_factorial():
    # This program fails we got it from his decompilation
    # however changing the order of load and incr at off set 0x3 and 0x2
    # fixes it
    program = {
        "max_stack": 2,
        "max_locals": 2,
        "exceptions": [],
        "stack_map": [
            {"index": 2, "type": "append_frame", "info": [{"type": "integer"}]},
            {"index": 10, "type": "same"},
        ],
        "bytecode": [
            {"offset": 0, "opr": "load", "type": "int", "index": 0},
            {"offset": 1, "opr": "store", "type": "int", "index": 1},
            {"offset": 2, "opr": "load", "type": "int", "index": 0},
            {"offset": 3, "opr": "incr", "index": 0, "amount": -1},
            {"offset": 6, "opr": "ifz", "condition": "le", "target": 10},
            {"offset": 9, "opr": "load", "type": "int", "index": 1},
            {"offset": 10, "opr": "load", "type": "int", "index": 0},
            {"offset": 11, "opr": "binary", "type": "int", "operant": "mul"},
            {"offset": 12, "opr": "store", "type": "int", "index": 1},
            {"offset": 13, "opr": "goto", "target": 2},
            {"offset": 16, "opr": "load", "type": "int", "index": 1},
            {"offset": 17, "opr": "return", "type": "int"},
        ],
    }

    fixed_program = {
        "max_stack": 2,
        "max_locals": 2,
        "exceptions": [],
        "stack_map": [
            {"index": 2, "type": "append_frame", "info": [{"type": "integer"}]},
            {"index": 10, "type": "same"},
        ],
        "bytecode": [
            {"offset": 0, "opr": "load", "type": "int", "index": 0},
            {"offset": 1, "opr": "store", "type": "int", "index": 1},
            {"offset": 3, "opr": "incr", "index": 0, "amount": -1},
            {"offset": 2, "opr": "load", "type": "int", "index": 0},
            {"offset": 6, "opr": "ifz", "condition": "le", "target": 10},
            {"offset": 9, "opr": "load", "type": "int", "index": 1},
            {"offset": 10, "opr": "load", "type": "int", "index": 0},
            {"offset": 11, "opr": "binary", "type": "int", "operant": "mul"},
            {"offset": 12, "opr": "store", "type": "int", "index": 1},
            {"offset": 13, "opr": "goto", "target": 2},
            {"offset": 16, "opr": "load", "type": "int", "index": 1},
            {"offset": 17, "opr": "return", "type": "int"},
        ],
    }

    interpreter = Interpreter(fixed_program, False)
    interpreter.run([[4], [], 0, None])
    assert interpreter.program_return == 24

    interpreter.run([[5], [], 0, None])
    assert interpreter.program_return == 120

    interpreter.run([[10], [], 0, None])
    assert interpreter.program_return == 3628800


def test_first():
    program = {
        "max_stack": 2,
        "max_locals": 1,
        "exceptions": [],
        "stack_map": None,
        "bytecode": [
            {"offset": 0, "opr": "load", "type": "ref", "index": 0},
            {"offset": 1, "opr": "push", "value": {"type": "integer", "value": 0}},
            {"offset": 2, "opr": "array_load", "type": "int"},
            {"offset": 3, "opr": "return", "type": "int"},
        ],
    }
    # Generate random array reference
    arr_ref = random.randint(1, 1000)
    state = [
        [arr_ref],
        [],
        0,
        None,
    ]  # local variables  # stackframes  # program counter
    test = Interpreter(program, False)
    # Generate random array in memory
    test.memory[arr_ref] = [
        random.randint(1, 100) for _ in range(random.randint(1, 20))
    ]
    test.run(state)
    assert test.program_return == test.memory[arr_ref][0]


def test_firstSafe():
    # Once we handle invoke, we should add bad path to this test
    program = {
        "max_stack": 2,
        "max_locals": 1,
        "exceptions": [],
        "stack_map": [{"index": 10, "type": "same"}],
        "bytecode": [
            {
                "offset": 0,
                "opr": "get",
                "static": True,
                "field": {
                    "class": "dtu/compute/exec/Array",
                    "name": "$assertionsDisabled",
                    "type": "boolean",
                },
            },
            {"offset": 3, "opr": "ifz", "condition": "ne", "target": 10},
            {"offset": 6, "opr": "load", "type": "ref", "index": 0},
            {"offset": 7, "opr": "arraylength"},
            {"offset": 8, "opr": "push", "value": {"type": "integer", "value": 1}},
            {"offset": 9, "opr": "if", "condition": "ge", "target": 10},
            {"offset": 12, "opr": "new", "class": "java/lang/AssertionError"},
            {"offset": 15, "opr": "dup", "words": 1},
            {
                "offset": 16,
                "opr": "invoke",
                "access": "special",
                "method": {
                    "is_interface": False,
                    "ref": {"kind": "class", "name": "java/lang/AssertionError"},
                    "name": "<init>",
                    "args": [],
                    "returns": None,
                },
            },
            {"offset": 19, "opr": "throw"},
            {"offset": 20, "opr": "load", "type": "ref", "index": 0},
            {"offset": 21, "opr": "push", "value": {"type": "integer", "value": 0}},
            {"offset": 22, "opr": "array_load", "type": "int"},
            {"offset": 23, "opr": "return", "type": "int"},
        ],
    }
    # Generate random array reference
    arr_ref = random.randint(1, 1000)
    state = [
        [arr_ref],
        [],
        0,
        None,
    ]  # local variables  # stackframes  # program counter
    test = Interpreter(program, False)
    # Generate random array in memory
    test.memory[arr_ref] = [
        random.randint(1, 100) for _ in range(random.randint(1, 20))
    ]
    # Add class static to memory
    test.memory["dtu/compute/exec/Array"] = {"$assertionsDisabled": 1}
    test.run(state)
    assert test.program_return == test.memory[arr_ref][0]


def test_firstSafe():
    # Once we handle invoke, we should add bad path to this test
    program = {
        "max_stack": 2,
        "max_locals": 2,
        "exceptions": [],
        "stack_map": None,
        "bytecode": [
            {"offset": 0, "opr": "load", "type": "ref", "index": 1},
            {"offset": 1, "opr": "load", "type": "int", "index": 0},
            {"offset": 2, "opr": "array_load", "type": "int"},
            {"offset": 3, "opr": "return", "type": "int"},
        ],
    }
    # Generate random array reference
    arr_ref = random.randint(1, 1000)
    test = Interpreter(program, False)
    # Generate random array in memory
    test.memory[arr_ref] = [
        random.randint(1, 100) for _ in range(random.randint(1, 20))
    ]
    # choose random index
    index = random.randint(0, len(test.memory[arr_ref]) - 1)
    state = [
        [index, arr_ref],
        [],
        0,
        None,
    ]  # local variables  # stackframes  # program counter
    test.run(state)
    assert test.program_return == test.memory[arr_ref][index]


def test_newArray():
    program = {
        "max_stack": 4,
        "max_locals": 1,
        "exceptions": [],
        "stack_map": None,
        "bytecode": [
            {"offset": 0, "opr": "push", "value": {"type": "integer", "value": 3}},
            {"offset": 1, "opr": "newarray", "dim": 1, "type": "int"},
            {"offset": 3, "opr": "dup", "words": 1},
            {"offset": 4, "opr": "push", "value": {"type": "integer", "value": 0}},
            {"offset": 5, "opr": "push", "value": {"type": "integer", "value": 1}},
            {"offset": 6, "opr": "array_store", "type": "int"},
            {"offset": 7, "opr": "dup", "words": 1},
            {"offset": 8, "opr": "push", "value": {"type": "integer", "value": 1}},
            {"offset": 9, "opr": "push", "value": {"type": "integer", "value": 2}},
            {"offset": 10, "opr": "array_store", "type": "int"},
            {"offset": 11, "opr": "dup", "words": 1},
            {"offset": 12, "opr": "push", "value": {"type": "integer", "value": 2}},
            {"offset": 13, "opr": "push", "value": {"type": "integer", "value": 3}},
            {"offset": 14, "opr": "array_store", "type": "int"},
            {"offset": 15, "opr": "store", "type": "ref", "index": 0},
            {"offset": 16, "opr": "load", "type": "ref", "index": 0},
            {"offset": 17, "opr": "push", "value": {"type": "integer", "value": 2}},
            {"offset": 18, "opr": "array_load", "type": "int"},
            {"offset": 19, "opr": "return", "type": "int"},
        ],
    }

    state = [[], [], 0, ("main","newarray")]  # local variables  # stackframes  # program counter
    test = Interpreter(program, False)
    test.run(state)
    assert test.program_return == 3


def test_aWierdOneWithinBounds():
    program = {
        "max_stack": 4,
        "max_locals": 1,
        "exceptions": [],
        "stack_map": None,
        "bytecode": [
            {"offset": 0, "opr": "push", "value": {"type": "integer", "value": 3}},
            {"offset": 1, "opr": "newarray", "dim": 1, "type": "int"},
            {"offset": 3, "opr": "dup", "words": 1},
            {"offset": 4, "opr": "push", "value": {"type": "integer", "value": 0}},
            {"offset": 5, "opr": "push", "value": {"type": "integer", "value": 0}},
            {"offset": 6, "opr": "array_store", "type": "int"},
            {"offset": 7, "opr": "dup", "words": 1},
            {"offset": 8, "opr": "push", "value": {"type": "integer", "value": 1}},
            {"offset": 9, "opr": "push", "value": {"type": "integer", "value": 1}},
            {"offset": 10, "opr": "array_store", "type": "int"},
            {"offset": 11, "opr": "dup", "words": 1},
            {"offset": 12, "opr": "push", "value": {"type": "integer", "value": 2}},
            {"offset": 13, "opr": "push", "value": {"type": "integer", "value": 4}},
            {"offset": 14, "opr": "array_store", "type": "int"},
            {"offset": 15, "opr": "store", "type": "ref", "index": 0},
            {"offset": 16, "opr": "load", "type": "ref", "index": 0},
            {"offset": 17, "opr": "load", "type": "ref", "index": 0},
            {"offset": 18, "opr": "push", "value": {"type": "integer", "value": 1}},
            {"offset": 19, "opr": "array_load", "type": "int"},
            {"offset": 20, "opr": "array_load", "type": "int"},
            {"offset": 21, "opr": "return", "type": "int"},
        ],
    }

    state = [[], [], 0, None]  # local variables  # stackframes  # program counter
    test = Interpreter(program, False)
    test.run(state)
    assert test.program_return == 1


def test_newArrayOutOfBounds():
    program = {
        "max_stack": 4,
        "max_locals": 1,
        "exceptions": [],
        "stack_map": None,
        "bytecode": [
            {"offset": 0, "opr": "push", "value": {"type": "integer", "value": 3}},
            {"offset": 1, "opr": "newarray", "dim": 1, "type": "int"},
            {"offset": 3, "opr": "dup", "words": 1},
            {"offset": 4, "opr": "push", "value": {"type": "integer", "value": 0}},
            {"offset": 5, "opr": "push", "value": {"type": "integer", "value": 1}},
            {"offset": 6, "opr": "array_store", "type": "int"},
            {"offset": 7, "opr": "dup", "words": 1},
            {"offset": 8, "opr": "push", "value": {"type": "integer", "value": 1}},
            {"offset": 9, "opr": "push", "value": {"type": "integer", "value": 2}},
            {"offset": 10, "opr": "array_store", "type": "int"},
            {"offset": 11, "opr": "dup", "words": 1},
            {"offset": 12, "opr": "push", "value": {"type": "integer", "value": 2}},
            {"offset": 13, "opr": "push", "value": {"type": "integer", "value": 3}},
            {"offset": 14, "opr": "array_store", "type": "int"},
            {"offset": 15, "opr": "store", "type": "ref", "index": 0},
            {"offset": 16, "opr": "load", "type": "ref", "index": 0},
            {"offset": 17, "opr": "push", "value": {"type": "integer", "value": 4}},
            {"offset": 18, "opr": "array_load", "type": "int"},
            {"offset": 19, "opr": "return", "type": "int"},
        ],
    }

    state = [[], [], 0, None]  # local variables  # stackframes  # program counter
    test = Interpreter(program, False)
    with pytest.raises(IndexError) as e:
        test.run(state)


def test_aWierdOneOutOfBounds():
    program = {
        "max_stack": 4,
        "max_locals": 1,
        "exceptions": [],
        "stack_map": None,
        "bytecode": [
            {"offset": 0, "opr": "push", "value": {"type": "integer", "value": 3}},
            {"offset": 1, "opr": "newarray", "dim": 1, "type": "int"},
            {"offset": 3, "opr": "dup", "words": 1},
            {"offset": 4, "opr": "push", "value": {"type": "integer", "value": 0}},
            {"offset": 5, "opr": "push", "value": {"type": "integer", "value": 0}},
            {"offset": 6, "opr": "array_store", "type": "int"},
            {"offset": 7, "opr": "dup", "words": 1},
            {"offset": 8, "opr": "push", "value": {"type": "integer", "value": 1}},
            {"offset": 9, "opr": "push", "value": {"type": "integer", "value": 1}},
            {"offset": 10, "opr": "array_store", "type": "int"},
            {"offset": 11, "opr": "dup", "words": 1},
            {"offset": 12, "opr": "push", "value": {"type": "integer", "value": 2}},
            {"offset": 13, "opr": "push", "value": {"type": "integer", "value": 4}},
            {"offset": 14, "opr": "array_store", "type": "int"},
            {"offset": 15, "opr": "store", "type": "ref", "index": 0},
            {"offset": 16, "opr": "load", "type": "ref", "index": 0},
            {"offset": 17, "opr": "load", "type": "ref", "index": 0},
            {"offset": 18, "opr": "push", "value": {"type": "integer", "value": 2}},
            {"offset": 19, "opr": "array_load", "type": "int"},
            {"offset": 20, "opr": "array_load", "type": "int"},
            {"offset": 21, "opr": "return", "type": "int"},
        ],
    }

    state = [[], [], 0, None]  # local variables  # stackframes  # program counter
    test = Interpreter(program, False)
    with pytest.raises(IndexError) as e:
        test.run(state)


def test_fib():
    # There's a bug in the test decompilation so it always return 1
    class_obj = utils.load_class(f"../decompiled/Calls.json")
    program = utils.load_method("fib", class_obj)

    state = [[5], [], 0, ("fib","dtu/compute/exec/Calls")]  # local variables  # stackframes  # program counter
    test = Interpreter(program, True)
    test.code_memory["dtu/compute/exec/Calls"] = class_obj
    test.run(state)
    assert test.program_return == 5

    class_obj = utils.load_class(f"../decompiled/Calls.json")
    program = utils.load_method("fib", class_obj)

    state = [[6], [], 0, ("fib","dtu/compute/exec/Calls")]  # local variables  # stackframes  # program counter
    test = Interpreter(program, True)
    test.code_memory["dtu/compute/exec/Calls"] = class_obj
    test.run(state)

    assert test.program_return == 8

    class_obj = utils.load_class(f"../decompiled/Calls.json")
    program = utils.load_method("fib", class_obj)

    state = [[7], [], 0, ("fib","dtu/compute/exec/Calls")]  # local variables  # stackframes  # program counter
    test = Interpreter(program, True)
    test.code_memory["dtu/compute/exec/Calls"] = class_obj
    test.run(state)

    assert test.program_return == 13


def test_class_init():
    entry_class = utils.load_class(
        "../TestPrograms/ClassInstances/out/production/ClassInstances/Main.json")
    entry_function = utils.load_method("CreateClassInstance", entry_class)
    program = utils.load_program(
        "../TestPrograms/ClassInstances/out/production/ClassInstances")

    state = [[], [], 0, (
        "CreateClassInstance",
        "Main")]  # local variables  # stackframes  # program counter # (invoker_func,invoker_class)
    test = Interpreter(entry_function, True)
    test.load_program_into_memory(program)

    test.run(state)
    print(test.memory)
    objs = list(test.memory.keys())
    assert len(objs) == 1
    objref = objs[0]
    assert "PublicProperty" in test.memory[objref]
    assert "PrivateProperty" in test.memory[objref]
    assert test.memory[objref]["PublicProperty"] == 1
    assert test.memory[objref]["PrivateProperty"] == 2

def test_class_return_attr():
    entry_class = utils.load_class(
        "../TestPrograms/ClassInstances/out/production/ClassInstances/Main.json")
    entry_function = utils.load_method("InvokeMethod", entry_class)
    program = utils.load_program(
        "../TestPrograms/ClassInstances/out/production/ClassInstances")

    state = [["Test"], [], 0, (
        "InvokeMethod", "Main")]  # local variables  # stackframes  # program counter # (invoker_func,invoker_class)
    test = Interpreter(entry_function, True)
    test.load_program_into_memory(program)

    test.run(state)
    assert test.program_return == 2