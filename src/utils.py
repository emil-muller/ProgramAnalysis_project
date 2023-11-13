import json
import os


def load_class(path):
    with open(path, "r") as f:
        json_txt = f.read()
    return json.loads(json_txt)


def load_method(name, class_json, params=None):
    print("---------------------------")
    print(class_json)
    print("---------------------------")
    print(params)
    possible_methods = []
    for method in class_json["methods"]:
        if method["name"] != name:
            print("wtf")
            continue
        print("wtf2")
        method_params = [p["type"]["base"] for p in method["params"]]
        if method_params == params:
            return method["code"]
    return None


# Assumes all decompiled json files necessary for the program
# is in the same folder
def load_program(path):
    json_files_in_path = list(
        filter(lambda file: file.endswith(".json"), os.listdir(path))
    )
    classes_to_load = [path+"/"+file for file in json_files_in_path]
    classes = [load_class(c) for c in classes_to_load]
    return classes


def lookup_interface_method(interpreter, b, objref):
    # When we have testcases, expand this to support recursive lookups
    class_name = b["method"]["ref"]["name"]
    method_name = b["method"]["name"]
    params_types = b["method"]["args"]

    objref_class = interpreter.memory[objref]["class"]

    # Find method
    method = method = load_method(
        method_name, interpreter.code_memory[objref_class], params_types
    )
    return method


def lookup_virtual_and_static_method(interpreter, b):
    method = None
    class_name = b["method"]["ref"]["name"]
    method_name = b["method"]["name"]
    params_types = b["method"]["args"]
    try:
        method = load_method(
            method_name, interpreter.code_memory[class_name], params_types
        )
    except KeyError as e:
        print("Method not in class, trying superclass")

    # Handle inheritance.
    # Danger! Assumes call is either to known class or call to java std
    # If not this will run forever
    while not method:
        if class_name.startswith("java/"):
            break

        super_class = interpreter.code_memory[class_name]["super"]["name"]
        method = load_method(
            method_name, interpreter.code_memory[super_class], params_types
        )

        if method:
            return method

        class_name = super_class

    return method


def to_plantuml(call_trace, interpreter):
    uml_str = "@startuml\n"
    for invoker, invokee, type in call_trace:
        if type == "invoke":
            if invokee[0] != "<init>" or interpreter.verbose:
                uml_str += f'"{invoker[1]}" -> "{invokee[1]}" : {invokee[0]}\n'
        elif type == "return":
            if invoker[0] != "<init>" or interpreter.verbose:
                uml_str += f'"{invokee[1]}" <-- "{invoker[1]}" : {invoker[0]}\n'
    uml_str += "@enduml"
    return uml_str
