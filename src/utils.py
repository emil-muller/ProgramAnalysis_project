import json
import os


def load_class(path):
    with open(path, "r") as f:
        json_txt = f.read()
    return json.loads(json_txt)

def debug_print(debug: bool, print_str: str):
    if debug:
        print(print_str)

def load_method(name, class_json, params=None):
    for method in class_json["methods"]:
        if method["name"] == name:
            return method
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

    # If handle Bytecode and raw method access
    if isinstance(b, dict):
        class_name = b["method"]["ref"]["name"]
        method_name = b["method"]["name"]
        params_types = b["method"]["args"]
    else:
        class_name = b.method["ref"]["name"]
        method_name = b.method["name"]
        params_types = b.method["args"]

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


def to_plantuml_concolic(call_trace, params, interpreter, out_params):
    uml_lst = ["@startuml"]
    i = 0;
    for invoker, invokee, type in call_trace:
        if type == "invoke":
            if invokee[0] != "<init>" or interpreter.verbose:
                if i in params:
                    out_params[len(uml_lst)] = params[i]
                uml_lst.append(f'"{invoker[1]}" -> "{invokee[1]}" : {invokee[0]}')
        elif type == "return":
            if invoker[0] != "<init>" or interpreter.verbose:
                if i in params:
                    out_params[len(uml_lst)] = params[i]
                uml_lst.append(f'"{invokee[1]}" <-- "{invoker[1]}" : {invoker[0]}')
        i += 1
    uml_lst.append("@enduml")

    return uml_lst

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

    in_calls = 0
    out_calls = 0
    for call in match_lst:
        if "->" in call:
            out_calls += 1

        if "<--" in call:
            in_calls += 1
    return in_calls == out_calls

def compress_plantuml(uml_lst):
    uml_len = len(uml_lst)
    for n in range(1, len(uml_lst)-1):
        for i in range(1, len(uml_lst)-n):
            match = uml_lst[i:i+n]
            if not validate_match(match):
                continue

            k = 1
            non_compressable = False
            while True:
                if i+(k+1)*n < uml_len and match == uml_lst[i+n*k:i+(k+1)*n]:
                    k += 1
                else:
                    if k > 1:
                        #match was found, make edit and call again
                        new_uml_lst = []
                        #append all before match
                        for x in range(0, i):
                            new_uml_lst.append(uml_lst[x])

                        #add match
                        new_uml_lst.append(f"group repetition {k}")
                        new_uml_lst += match
                        new_uml_lst.append("end")

                        #Append all after match
                        for x in range(i+k*n, uml_len):
                            new_uml_lst.append(uml_lst[x])

                        return compress_plantuml(new_uml_lst)
                    break
    return uml_lst


class IndexOption:
    def __init__(self, option):
        self. index = 0
        self.option = option

    def copy(self):
        new_index_option = IndexOption(self.option)
        new_index_option.index = self.index
        return new_index_option

def all_match(indicies, umls):
    first_one = umls[0][indicies[0].index]
    for i in range(0, len(umls)):
        if umls[i][indicies[i].index] != first_one:
            return False
    return True


def increment_indicies(indicies):
    for index in indicies:
        index.index += 1


def all_contains(line, difs):
    for i in range(0,len(difs)):
        if line not in difs[i]:
            return False
    return True


def combine_if_identical(groups, options): #groups and options must be same length and they will be, trust me
    new_groups = []
    new_options = []
    for i in range(0,len(groups)):
        for k in range(0,len(groups)):
            if not groups[i][0] == groups[k][0] and groups[i][1:-1] == groups[k][1:-1]:
                new_groups.append([f"group Options {options[i]}, {options[k]}"])
                new_groups[i] += groups[i][1:-1]
                new_groups[i].append("end")
                new_options.append(f"{options[i]}, {options[k]}")
                del(groups[k]) # remove the group k now merged with i, here i < k always
                del(options[k])
                for j in range(i + 1, len(groups)): # we have combined add remaining groups and call recursively
                    new_options.append(options[j])
                    new_groups.append(groups[j])
                return combine_if_identical(new_groups, new_options)
        #no merge was found for groups[i]
        new_groups.append(groups[i])
        new_options.append(options[i])
    return new_groups

def combine_if_identical2(groups, options): #groups and options must be same length and they will be, trust me
    new_groups = []
    new_options = []
    for i in range(0, len(groups)):
        for k in range(0, len(groups)):
            if not groups[i][0] == groups[k][0] and len(groups[i]) == len(groups[k]):
                flag = True
                note = ""
                for j in range(1, len(groups[i])):
                    if groups[i][j] != groups[k][j] and "note" not in groups[k][j] and "note" not in groups[i][j]:
                        flag = False
                    elif "note" in groups[k][j] and "note" in groups[i][j]:
                        note = groups[k][j]
                if flag:
                    if len(groups[i][1:-1]) > 0:
                        new_groups.append([f"group Options {options[i]}, {options[k]}"])
                        new_groups[i] += groups[i][1:-1]
                        new_groups[i].append(note)
                        new_groups[i].append("end")
                        new_options.append(f"{options[i]}, {options[k]}")
                    del(groups[k]) # remove the group k now merged with i, here i < k always
                    del(options[k])
                    for j in range(i + 1, len(groups)): # we have combined add remaining groups and call recursively
                        if len(groups[j][1:-1]) > 0:
                            new_options.append(options[j])
                            new_groups.append(groups[j])
                    return combine_if_identical2(new_groups, new_options)

        #no merge was found for groups[i]
        new_groups.append(groups[i])
        new_options.append(options[i])
    return new_groups

def combine_diagrams(umls, prog_returns):
    first = 0
    while len(umls[first]) == 0:
        first+=1
        if first>=len(umls):
            return []
    attach_note_to = umls[first][0].split(" ->")[0]
    uml_lst = []
    append_to_end = []
    #initialize index list
    indicies = []
    for i in range(0, len(umls)):
        indicies.append(IndexOption(i))

    while True:
        deleted_options = False
        indicies_to_be_deleted = []
        for i in range(0, len(umls)): # remove indicies that are done
            if indicies[i].index >= len(umls[i]):
                uml_lst.append(f"note right {attach_note_to}: Option({indicies[i].option}) {prog_returns[indicies[i].option]}")
                indicies_to_be_deleted.append((indicies[i], umls[i]))
                deleted_options = True

        if deleted_options: # create new group with remaining indicies
            for i in indicies_to_be_deleted:
                (index, uml) = i
                indicies.remove(index)
                umls.remove(uml)
            if umls: # only add if some are still left
                uml_lst.append(f"group Option(s) [{','.join([f'{index.option}' for index in indicies])}]")
                append_to_end.append("end")

        if not umls: # No more to merge so we are done
            uml_lst += append_to_end
            return uml_lst

        if all_match(indicies, umls): # all match so append next call
            uml_lst.append(umls[0][indicies[0].index])
        else: #they dont match
            difs = []
            for i in range(0, len(umls)):
                difs.append([umls[i][indicies[i].index]])
            split_indicies = [index.copy() for index in indicies]

            while True:
                dont_break = False
                for i in range(0, len(difs)): #if any has gotten a call all contains, collapse to options
                    if all_contains(difs[i][-1], difs): # found the common one
                        groups = []
                        for k in range(0, len(difs)):
                            diff_index = difs[k].index(difs[i][-1]) # get index for common item
                            groups.append([f"group Option {indicies[k].option}"])
                            groups[k] += difs[k][0 : diff_index]
                            groups[k].append("end")
                            indicies[k].index = split_indicies[k].index + diff_index - 1 # Continue after shared item
                        groups = combine_if_identical2(groups, [f"{index.option}" for index in indicies])
                        for group in groups:
                            uml_lst += group
                        break
                else:
                    dont_break = True
                if not dont_break:
                    break # funky python logic

                increment_indicies(indicies)

                #again check if one or more is finished
                deleted_options = False
                indicies_to_be_deleted = []
                groups = []
                indexoptions = []
                for i in range(0, len(umls)):  # remove indicies that are done
                    if indicies[i].index >= len(umls[i]):
                        group = []
                        deleted_options = True
                        group.append(f"group Option {indicies[i].option}")
                        group += difs[i]
                        group.append(f"note right {attach_note_to}: Option({indicies[i].option}) {prog_returns[indicies[i].option]}")
                        group.append("end")
                        groups.append(group)
                        indexoptions.append(indicies[i].option)
                        indicies_to_be_deleted.append((indicies[i], umls[i]))
                groups = combine_if_identical2(groups, indexoptions)
                for group in groups:
                    uml_lst += group
                if deleted_options:  # create new group with remaining indicies
                    for i in indicies_to_be_deleted:
                        (index, uml) = i
                        indicies.remove(index)
                        umls.remove(uml)
                    if umls:  # only add if some are still left
                        uml_lst.append(f"group Option(s) [{','.join([f'{index.option}' for index in indicies])}]")
                        append_to_end.append("end")
                    # Reset diffs as the holdout might be in the deleted
                    difs = []
                    for i in range(0, len(umls)):
                        indicies[i].index = split_indicies[i].index
                        difs.append([umls[i][indicies[i].index]])

                if not umls:  # No more to merge so we are done
                    uml_lst += append_to_end
                    return uml_lst

                if len(umls) == 1: # special case if all but one has been finished
                    indicies[0].index -= 1 #it was incremented by one for diff that is now to be ignored
                    break

                for i in range(0, len(umls)):
                    difs[i].append(umls[i][indicies[i].index])
        increment_indicies(indicies)

def append_method_variables(uml, call_params):
    uml_new = []
    for i in range(0, len(uml)):
        if i in call_params:
            parsed_params = [call_params[i][k].concrete if not isinstance(call_params[i][k].concrete, str) or "_" not in call_params[i][k].concrete else "ref" for k in call_params[i]]
            uml_new.append(uml[i] + f"({parsed_params})")
        else:
            uml_new.append(uml[i])
    return uml_new

def final_sequence_diagram_concolic(call_traces, call_trace_params, interpreter):
    plant = []
    plant_params = []
    for i in range(0, len(call_traces)):
        plant_param = {}
        plant.append(to_plantuml_concolic(call_traces[i], call_trace_params[i], interpreter, plant_param)[1:-1])
        # plant_params.append(plant_param)
    # print(plant_params)
    #for i in range(0, len(plant)):
    #    print("\n".join(append_method_variables(plant[i], plant_params[i])))
    #    print()
    #plant = [to_plantuml(trace, call_trace_params[i], interpreter)[1:-1] for i, trace in call_traces]
    combined_plant = ["@startuml"] + combine_diagrams(plant, interpreter.prog_returns) + ["@enduml"]
    return '\n'.join(compress_plantuml(combined_plant))

def final_sequence_diagram(call_trace, interpreter, prog_returns):
    plant = ["@startuml"] + to_plantuml(call_trace, interpreter)[1:-1] + ["@enduml"]
    return '\n'.join(compress_plantuml(plant))