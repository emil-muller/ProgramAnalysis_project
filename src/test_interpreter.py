import random
import uuid
import pytest
import utils
from bytecode_interpreter import Interpreter
from concolic_interpreter import ConcolicInterpreter


def test_zero():
    class_obj = utils.load_class(f"../decompiled/Simple.json")
    program = utils.load_method("zero", class_obj, [])

    state = [[], [], 0, ("zero", "dtu/compute/exec/Simple", [])]
    interpreter = Interpreter(program, False)
    interpreter.code_memory["dtu/compute/exec/Calls"] = class_obj
    interpreter.run(state)
    assert interpreter.program_return == 0


def test_hundredAndTwo():
    class_obj = utils.load_class(f"../decompiled/Simple.json")
    program = utils.load_method("hundredAndTwo", class_obj, [])

    state = [[], [], 0, ("hundredAndTwo", "dtu/compute/exec/Simple", [])]
    interpreter = Interpreter(program, False)
    interpreter.code_memory["dtu/compute/exec/Calls"] = class_obj
    interpreter.run(state)
    assert interpreter.program_return == 102


def test_identity():
    class_obj = utils.load_class(f"../decompiled/Simple.json")
    program = utils.load_method("identity", class_obj, [])

    state = [[420], [], 0, ("identity", "dtu/compute/exec/Simple", [])]
    interpreter = Interpreter(program, False)
    interpreter.code_memory["dtu/compute/exec/Calls"] = class_obj
    interpreter.run(state)
    assert interpreter.program_return == 420


def test_add():
    class_obj = utils.load_class(f"../decompiled/Simple.json")
    program = utils.load_method("add", class_obj, [])

    state = [[420, 69], [], 0, ("add", "dtu/compute/exec/Simple", [])]
    interpreter = Interpreter(program, False)
    interpreter.code_memory["dtu/compute/exec/Calls"] = class_obj
    interpreter.run(state)
    assert interpreter.program_return == 489


def test_min():
    class_obj = utils.load_class(f"../decompiled/Simple.json")
    program = utils.load_method("min", class_obj, [])

    interpreter = Interpreter(program, False)
    interpreter.code_memory["dtu/compute/exec/Calls"] = class_obj

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
        "code": {
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
    }

    interpreter = Interpreter(fixed_program, False)
    interpreter.run([[4], [], 0, None])
    assert interpreter.program_return == 24

    interpreter.run([[5], [], 0, None])
    assert interpreter.program_return == 120

    interpreter.run([[10], [], 0, None])
    assert interpreter.program_return == 3628800


def test_first():
    class_obj = utils.load_class(f"../decompiled/Array.json")
    program = utils.load_method("first", class_obj, [])

    interpreter = Interpreter(program, False)
    interpreter.code_memory["dtu/compute/exec/Calls"] = class_obj

    # Generate random array reference
    arr_ref = f"Array_{uuid.uuid4()}"
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


def test_access():
    # Once we handle invoke, we should add bad path to this test
    class_obj = utils.load_class(f"../decompiled/Array.json")
    program = utils.load_method("access", class_obj, [])

    interpreter = Interpreter(program, False)
    interpreter.code_memory["dtu/compute/exec/Calls"] = class_obj

    # Generate random array reference
    arr_ref = f"Array_{uuid.uuid4()}"
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
    class_obj = utils.load_class(f"../decompiled/Array.json")
    program = utils.load_method("newArray", class_obj, [])

    interpreter = Interpreter(program, False)
    interpreter.code_memory["dtu/compute/exec/Calls"] = class_obj

    state = [[], [], 0, ("main", "newArray")]  # local variables  # stackframes  # program counter
    test = Interpreter(program, False)
    test.run(state)
    assert test.program_return == 1


def test_aWierdOneWithinBounds():
    class_obj = utils.load_class(f"../decompiled/Array.json")
    program = utils.load_method("aWierdOneWithinBounds", class_obj, [])

    interpreter = Interpreter(program, False)
    interpreter.code_memory["dtu/compute/exec/Calls"] = class_obj

    state = [[], [], 0, None]  # local variables  # stackframes  # program counter
    test = Interpreter(program, False)
    test.run(state)
    assert test.program_return == 1


def test_newArrayOutOfBounds():
    class_obj = utils.load_class(f"../decompiled/Array.json")
    program = utils.load_method("newArrayOutOfBounds", class_obj, [])

    interpreter = Interpreter(program, False)
    interpreter.code_memory["dtu/compute/exec/Calls"] = class_obj

    state = [[], [], 0, None]  # local variables  # stackframes  # program counter
    test = Interpreter(program, False)
    with pytest.raises(IndexError) as e:
        test.run(state)


def test_aWierdOneOutOfBounds():
    class_obj = utils.load_class(f"../decompiled/Array.json")
    program = utils.load_method("aWierdOneOutOfBounds", class_obj, [])

    interpreter = Interpreter(program, False)
    interpreter.code_memory["dtu/compute/exec/Calls"] = class_obj

    state = [[], [], 0, None]  # local variables  # stackframes  # program counter
    test = Interpreter(program, False)
    with pytest.raises(IndexError) as e:
        test.run(state)


def test_fib():
    # There's a bug in the test decompilation, so it always return 1
    class_obj = utils.load_class(f"../decompiled/Calls.json")
    program = utils.load_method("fib", class_obj, ["int"])

    state = [[5], [], 0, ("fib", "dtu/compute/exec/Calls", ["int"])] 
    test = Interpreter(program, False)
    test.code_memory["dtu/compute/exec/Calls"] = class_obj
    test.run(state)
    assert test.program_return == 8

    class_obj = utils.load_class(f"../decompiled/Calls.json")
    program = utils.load_method("fib", class_obj, ["int"])

    state = [[6], [], 0, ("fib", "dtu/compute/exec/Calls", ["int"])]
    test = Interpreter(program, False)
    test.code_memory["dtu/compute/exec/Calls"] = class_obj
    test.run(state)

    assert test.program_return == 13

    class_obj = utils.load_class(f"../decompiled/Calls.json")
    program = utils.load_method("fib", class_obj, ["int"])

    state = [[7], [], 0, ("fib", "dtu/compute/exec/Calls", ["int"])]
    test = Interpreter(program, False)
    test.code_memory["dtu/compute/exec/Calls"] = class_obj
    test.run(state)

    assert test.program_return == 21


def test_class_init():
    entry_class = utils.load_class(
        "../TestPrograms/ClassInstances/out/production/ClassInstances/Main.json")
    entry_function = utils.load_method("CreateClassInstance", entry_class, [])
    program = utils.load_program(
        "../TestPrograms/ClassInstances/out/production/ClassInstances")

    state = [[], [], 0, (
        "CreateClassInstance",
        "Main", [])]  # local variables  # stackframes  # program counter # (invoker_func,invoker_class)
    test = Interpreter(entry_function, False)
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
    entry_function = utils.load_method("InvokeMethod", entry_class, [])
    program = utils.load_program(
        "../TestPrograms/ClassInstances/out/production/ClassInstances")

    state = [["Test"], [], 0, (
        "InvokeMethod", "Main", [])]  # local variables  # stackframes  # program counter # (invoker_func,invoker_class)
    test = Interpreter(entry_function, False)
    test.load_program_into_memory(program)

    test.run(state)
    assert test.program_return == 2


def test_simple_inheritance():
    entry_class = utils.load_class(
        "../TestPrograms/Inheritance/out/production/Inheritance/Main.json")
    entry_function = utils.load_method("CallsInheritedVoidMethod", entry_class, [])
    program = utils.load_program(
        "../TestPrograms/Inheritance/out/production/Inheritance")

    state = [["Test"], [], 0, (
        "CallsInheritedVoidMethod", "Main", [])]
    test = Interpreter(entry_function, False)
    test.load_program_into_memory(program)

    test.run(state)
    objs = list(test.memory.keys())
    assert len(objs) == 1
    objref = objs[0]
    assert "A" in test.memory[objref]
    assert "B" in test.memory[objref]
    assert test.memory[objref]["A"] == 1
    assert test.memory[objref]["B"] == 2


def test_get_inherited_props():
    entry_class = utils.load_class(
        "../TestPrograms/Inheritance/out/production/Inheritance/Main.json")
    entry_function = utils.load_method("GetsInheritedProperty", entry_class, [])
    program = utils.load_program(
        "../TestPrograms/Inheritance/out/production/Inheritance")

    state = [["Test"], [], 0, (
        "GetsInheritedProperty", "Main",
        [])]  # local variables  # stackframes  # program counter # (invoker_func,invoker_class)
    test = Interpreter(entry_function, False)
    test.load_program_into_memory(program)

    test.run(state)
    assert test.program_return == 1


def test_interface():
    entry_class = utils.load_class(
        "../TestPrograms/Inheritance/out/production/Inheritance/Main.json")
    entry_function = utils.load_method("CallsInterfaceMethodWithInterface", entry_class, [])
    program = utils.load_program(
        "../TestPrograms/Inheritance/out/production/Inheritance")

    state = [["Test"], [], 0, (
        "CallsInterfaceMethodWithInterface", "Main", [])]
    test = Interpreter(entry_function, False)
    test.load_program_into_memory(program)

    test.run(state)
    assert not test.program_return