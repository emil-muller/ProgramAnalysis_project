import json
import os


def load_class(path):
    with open(path, "r") as f:
        json_txt = f.read()
    return json.loads(json_txt)


def load_method(name, class_json, params=None):
    for method in class_json["methods"]:
        if method["name"] == name:
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
    method = load_method(
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
    uml_lst = ["@startuml"]
    for invoker, invokee, type in call_trace:
        if type == "invoke":
            if invokee[0] != "<init>" or interpreter.verbose:
                uml_lst.append(f'"{invoker[1]}" -> "{invokee[1]}" : {invokee[0]}')
        elif type == "return":
            if invoker[0] != "<init>" or interpreter.verbose:
                uml_lst.append(f'"{invokee[1]}" <-- "{invoker[1]}" : {invoker[0]}')
    uml_lst.append("@enduml")

    return uml_lst


def validate_match(match_lst):
    if "->" not in match_lst[0]:
        return False

    if "<--" not in match_lst[-1]:
        return False

    in_calls = 0
    out_calls = 0
    for call in match_lst:
        if "->" in call:
            out_calls += 1

        if "<--" in call:
            in_calls += 1
    return in_calls == out_calls

def compress_plantuml(uml_lst):
    compressed_uml = []
    uml_len = len(uml_lst)
    for n in range(1, len(uml_lst)-1):
        for i in range(1, len(uml_lst)-n):
            match = uml_lst[i:i+n]
            if not validate_match(match):
                continue

            k = 1
            while True:
                if i+(k+1)*n < uml_len and match == uml_lst[i+n*k:i+(k+1)*n]:
                    print(f"{i=}, {n=}, {k=}")
                    print(match)
                    print(uml_lst[i + n * k:i + (k + 1) * n])
                    k += 1
            #for k in range(1,(uml_len-i)//n):
            #    if match == uml_lst[i+n*k:i+(k+1)*n]:
            #        print(f"{i=}, {n=}, {k=}")
            #        print(match)
            #        print(uml_lst[i+n*k:i+(k+1)*n])'''
                else:
                    if k > 1:
                        #match was found, make edit and call again
                        new_uml_lst = []
                        #append all before match
                        for x in range(0, i):
                            new_uml_lst.append(uml_lst[x])

                        #add match
                        new_uml_lst.append(f"START LOOPS BROTHER {k}")
                        new_uml_lst += match
                        new_uml_lst.append("END LOOPS BROTHER")

                        #Append all after match
                        for x in range(i+k*n, uml_len):
                            new_uml_lst.append(uml_lst[x])

                        print(new_uml_lst)
                        print()
                        return compress_plantuml(new_uml_lst)
                    break

