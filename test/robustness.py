import argparse
import json
import os
import shutil
import subprocess

tlc_jar="/Users/idardik/bin/tla2tools.jar"
tlcian_jar="/Users/idardik/Documents/CMU/tlaplus-master/git/tlaplus/bin/tlc-ian.jar"
sep_source_path="/Users/idardik/Documents/CMU/folseparators-tla"


def const_constraint(jsonResult, key):
    if key in jsonResult:
        return jsonResult[key]
    else:
        return None

def non_const_constraint(jsonResult, outdir, key):
    if key in jsonResult:
        sep_file = jsonResult[key]
        return run_fol_separator(outdir, sep_file)
    else:
        return None

def load_sorts_map(sorts_map_file):
    file = open(sorts_map_file, "r")
    contents = file.read()
    return json.loads(contents)

def substituteTlaChars(form):
    return form.replace("Ss_sS", " ")\
        .replace("Qq_qQ", "\"")\
        .replace("Lp_pL", "{")\
        .replace("Rp_pR", "}")

def print_constraint(const, non_const, sorts_map_file):
    print("Safety boundary rep formula (with sort definitions):")
    if non_const is not None and sorts_map_file is not None:
        sorts_map = load_sorts_map(sorts_map_file)
        for k,v in sorts_map.items():
            if k in non_const:
                sort_def = k + " == " + v
                print(sort_def)
    if const is not None:
        conjuncts = const.split(", ")
        conj = "/\\ " + ("\n/\\ ".join(conjuncts))
        print(conj)
    if non_const is not None:
        conj = "/\\ " + substituteTlaChars(non_const)
        print(conj)

def run_fol_separator(outdir, sep_file):
    orig_dir = os.getcwd()
    os.chdir(sep_source_path)
    sep_path = orig_dir + "/" + sep_file
    cmd_args = ["python3", "-m", "separators", "--separate", "--no-cvc4", "--quiet", sep_path]
    result = subprocess.run(cmd_args, text=True, capture_output=True)
    os.chdir(orig_dir)

    if result.returncode != 0:
        print("FOL Separator tool failed with the following error:")
        print(result.stderr)
        return None

    lines = result.stdout.split("\n")
    # last line of stdout contains the json output
    jsonResult = json.loads(lines[-2])
    # TODO check for the error field in jsonResult
    return jsonResult["formula"]

def run_tlc_tool(cmd_args, outdir):
    #orig_dir = os.getcwd()
    #os.chdir(outdir)
    result = subprocess.run(cmd_args, text=True, capture_output=True)
    shutil.rmtree("states/")
    #os.remove(spec_name + "_TTrace*")
    #os.chdir(orig_dir)
    return result

def run_tlc_robust(spec_name, spec, cfg, outdir):
    cmd_args = ["java", "-jar", tlcian_jar, outdir, spec, cfg]
    result = run_tlc_tool(cmd_args, outdir)
    return json.loads(result.stdout)

def run_tlc_robust_compare(spec1_name, spec1, cfg1, spec2_name, spec2, cfg2, outdir):
    cmd_args = ["java", "-jar", tlcian_jar, outdir, spec1, cfg1, spec2, cfg2]
    result = run_tlc_tool(cmd_args, outdir)
    return json.loads(result.stdout)

def run_tlc_check(spec, cfg, outdir):
    cmd_args = ["java", "-jar", tlc_jar, "-deadlock", "-cleanup", "-config", cfg, spec]
    result = run_tlc_tool(cmd_args, outdir)

    # TLC exit code 0: ok
    # TLC exit code 12: safety violation
    # TLC exit code 13: liveness violation
    retCode = result.returncode
    assert retCode in [0,12,13], "TLC returned an unexpected return code: " + str(retCode)
    return retCode == 0

# check: err_x |= err_y
def err_satisfaction(err_pre_tla, err_post_tla, cfg, outdir):
    epre_sat = run_tlc_check(err_pre_tla, cfg, outdir)
    epost_sat = run_tlc_check(err_post_tla, cfg, outdir)
    return epre_sat and epost_sat

def get_spec_name(spec):
    assert spec[-4:] == ".tla", "specs must end in .tla extension"
    return spec[0:-4]

def get_cfg(spec_name, cfg):
    if cfg is not None:
        assert cfg[-4:] == ".cfg", "configs must end in .cfg extension"
        return cfg
    return spec_name + ".cfg"

def run_robustness(args):
    spec = args.spec
    spec_name = get_spec_name(spec)
    cfg = get_cfg(spec_name, args.config)
    outdir = args.outdir
    jsonResult = run_tlc_robust(spec_name, spec, cfg, outdir)

    assert jsonResult['comparison_type'] == 'spec_to_property'
    assert jsonResult['spec_name'] == spec_name

    if "diff_rep_state_formula_error" in jsonResult:
        err_msg = jsonResult["diff_rep_state_formula_error"]
        print("Found error while calculating robustness: " + err_msg)

    print("TLA+ Module: " + spec_name)
    print("Diff rep grouped by action:")
    spec_is_safe = jsonResult["spec_is_safe"]
    if spec_is_safe == "true":
        print("Spec is robust against ANY behavior or environment")
    else:
        diff_rep_states_empty = jsonResult["diff_rep_states_empty"]
        if diff_rep_states_empty == "true":
            print("the diff rep for eta(" + spec_name + ") is empty")
        else:
            group_names = jsonResult['group_names']
            for group in group_names:
                diff_rep_file = jsonResult['diff_rep_file_' + group]
                sorts_map_file = jsonResult['sorts_map_file_'+group] if ('sorts_map_file_'+group) in jsonResult else None
                const_constr = const_constraint(jsonResult, 'const_value_constraint_' + group)
                non_const_constr = non_const_constraint(jsonResult, outdir, 'separator_file_' + group)
                print()
                print(group + ":")
                print("Safety boundary representation: " + diff_rep_file)
                print_constraint(const_constr, non_const_constr, sorts_map_file)

def run_env(args):
    print("Not supported yet")

def run_comparison(args):
    spec1 = args.spec
    spec1_name = get_spec_name(spec1)
    cfg1 = get_cfg(spec1_name, args.config)
    spec2 = args.spec2
    spec2_name = get_spec_name(spec2)
    cfg2 = get_cfg(spec2_name, args.config2)
    outdir = args.outdir
    jsonResult = run_tlc_robust_compare(spec1_name, spec1, cfg1, spec2_name, spec2, cfg2, outdir)

    assert jsonResult['comparison_type'] == 'spec_to_spec'
    assert jsonResult['spec1_name'] == spec1_name
    assert jsonResult['spec2_name'] == spec2_name

    if "diff_rep_state_formula_error" in jsonResult:
        err_msg = jsonResult["diff_rep_state_formula_error"]
        print("Found error while calculating robustness: " + err_msg)

    spec1_is_safe = jsonResult["spec1_is_safe"]
    spec2_is_safe = jsonResult["spec2_is_safe"]

    # there is no safety/error boundary if at least one spec has no erroneous behaviors
    if spec1_is_safe == "true" and spec2_is_safe == "true":
        print("Both specs are robust against ANY behavior or environment, and therefore are equally robust.")
    elif spec1_is_safe == "true":
        print(spec1_name + " is robust against ANY behavior or environment, and is therefore strictly more robust than " + spec2_name + ".")
    elif spec2_is_safe == "true":
        print(spec2_name + " is robust against ANY behavior or environment, and is therefore strictly more robust than " + spec1_name + ".")
    else:
        combined_err_pre_tla = jsonResult['combined_err_pre_tla']
        combined_err_post_tla = jsonResult['combined_err_post_tla']
        spec1_sat_spec2_cfg = jsonResult['spec1_sat_spec2_cfg']
        spec2_sat_spec1_cfg = jsonResult['spec2_sat_spec1_cfg']

        # check: err1 |= err2? and
        # check: err2 |= err1?
        err1_satisfies_err2 = err_satisfaction(combined_err_pre_tla, combined_err_post_tla, spec1_sat_spec2_cfg, outdir)
        err2_satisfies_err1 = err_satisfaction(combined_err_pre_tla, combined_err_post_tla, spec2_sat_spec1_cfg, outdir)

        print("TLA+ Module Comparison: " + spec1_name + " v. " + spec2_name)
        if err1_satisfies_err2 and err2_satisfies_err1:
            print("The specs are equally robust")
        elif err1_satisfies_err2:
            print(spec1_name + " is strictly more robust than " + spec2_name)
        elif err2_satisfies_err1:
            print(spec2_name + " is strictly more robust than " + spec1_name)
        else:
            print("The robustness of the two specs are incomparable")

        # show \eta1-\eta2
        print()
        diff_rep_states1_empty = jsonResult["diff_rep_states1_empty"]
        if diff_rep_states1_empty == "false":
            print("Robustness comparison: eta(" + spec1_name + ") - eta(" + spec2_name + ")")
            print("Diff rep grouped by action:")
            group_names = jsonResult['group_names1']
            for group in group_names:
                diff_rep_file = jsonResult["diff_rep_file1_" + group]
                sorts_map_file = jsonResult['sorts_map_file1_'+group] if ('sorts_map_file1_'+group) in jsonResult else None
                const_constr = const_constraint(jsonResult, "const_value_constraint1_" + group)
                non_const_constr = non_const_constraint(jsonResult, outdir, "separator1_file_" + group)
                print()
                print(group + ":")
                print("Safety boundary representation: " + diff_rep_file)
                print_constraint(const_constr, non_const_constr, sorts_map_file)
        else:
            print("the diff rep for eta(" + spec1_name + ") - eta(" + spec2_name + ") is empty")

        # show \eta2-\eta1
        print()
        diff_rep_states2_empty = jsonResult["diff_rep_states2_empty"]
        if diff_rep_states2_empty == "false":
            print("Robustness comparison: eta(" + spec2_name + ") - eta(" + spec1_name + ")")
            print("Diff rep grouped by action:")
            group_names = jsonResult['group_names2']
            for group in group_names:
                diff_rep_file = jsonResult["diff_rep_file2_" + group]
                sorts_map_file = jsonResult['sorts_map_file2_'+group] if ('sorts_map_file2_'+group) in jsonResult else None
                const_constr = const_constraint(jsonResult, "const_value_constraint2_" + group)
                non_const_constr = non_const_constraint(jsonResult, outdir, "separator2_file_" + group)
                print()
                print(group + ":")
                print("Safety boundary representation: " + diff_rep_file)
                print_constraint(const_constr, non_const_constr, sorts_map_file)
        else:
            print("the diff rep for eta(" + spec2_name + ") - eta(" + spec1_name + ") is empty")

def create_args():
    parser = argparse.ArgumentParser(
        prog = "robustness",
        description = "Calculates and compares robustness for TLA+ specs")
    parser.add_argument("--outdir", required=True)
    parser.add_argument("--spec", required=True)
    parser.add_argument("--config")
    parser.add_argument("--spec2")
    parser.add_argument("--config2")
    parser.add_argument("--env", action="store_true")
    parser.add_argument("--compare", action="store_true")
    parser.add_argument("--cleanup", action="store_true")
    return parser.parse_args()

def run():
    args = create_args()
    os.makedirs(args.outdir, exist_ok=True)
    if args.env:
        run_env(args)
    elif args.compare:
        run_comparison(args)
    else:
        run_robustness(args)

    if args.cleanup:
        shutil.rmtree(args.outdir)

run()
