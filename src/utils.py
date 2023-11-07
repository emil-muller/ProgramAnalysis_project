import json
import os


def load_class(path):
    with open(path, "r") as f:
        json_txt = f.read()
    return json.loads(json_txt)

def load_method(name, class_json, params=None):
    possible_methods = []
    for method in class_json["methods"]:
        if method["name"] != name:
            continue
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
        super_class = class_name
        try:
            super_class = interpreter.code_memory[class_name]["super"]["name"]
            method = utils.load_method(
                method_name, interpreter.code_memory[super_class], params_types
            )
        except Exception as e:
            # Check if method is defined in ew super class
            class_name = super_class

            # Don't load system calls
            if super_class.startswith("java/"):
                break
    return method

