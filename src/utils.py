import json
import os


def load_class(path):
    with open(path, "r") as f:
        json_txt = f.read()
    return json.loads(json_txt)


def load_method(name, class_json):
    for method in class_json["methods"]:
        if method["name"] == name:
            return method["code"]


# Assumes all decompiled json files necessary for the program
# is in the same folder
def load_program(path):
    json_files_in_path = list(
        filter(lambda file: file.endswith(".json"), os.listdir(path))
    )
    classes_to_load = [path+"/"+file for file in json_files_in_path]
    classes = [load_class(c) for c in classes_to_load]

    return classes

def to_plantuml(call_trace):
    uml_str = "@startuml\n"
    print(call_trace)
    for invoker,invokee,type in call_trace:
        if type == "invoke":
            uml_str += f'"{invoker[1]}" -> "{invokee[1]}" : {invokee[0]}\n'
        elif type == "return":
            uml_str += f'"{invokee[1]}" <-- "{invoker[1]}" : {invoker[0]}\n'
    uml_str += "@enduml"
    return uml_str