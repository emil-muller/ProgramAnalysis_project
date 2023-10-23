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


# Assumes all decompiled json files necesssary for the program
# is in the same folder
def load_program(path):
    json_files_in_path = list(
        filter(lambda file: file.endswith(".json"), os.listdir(path))
    )
    classes = [load_class(c) for c in json_files_in_path]
    return classes
