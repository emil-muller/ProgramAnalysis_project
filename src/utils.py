import json


def load_class(path):
    with open(path, "r") as f:
        json_txt = f.read()
    return json.loads(json_txt)


def load_method(name, class_json):
    for method in class_json["methods"]:
        if method["name"] == name:
            return method["code"]
