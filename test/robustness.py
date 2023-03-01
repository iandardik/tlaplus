# result.returncode
# TLC exit code 12: safety violation
# TLC exit code 13: liveness violation

import argparse
import json
import os
import shutil
import subprocess

tlcian_jar="/Users/idardik/Documents/CMU/tlaplus-master/git/tlaplus/bin/tlc-ian.jar"
sep_source_path="/Users/idardik/Documents/CMU/folseparators"


def run_fol_separator(outdir, sep_file):
    orig_dir = os.getcwd()
    os.chdir(sep_source_path)
    sep_path = orig_dir + "/" + outdir + "/" + sep_file
    cmd_args = ["python3", "-m", "separators", "--separate", "--no-cvc4", "--quiet", sep_path]
    result = subprocess.run(cmd_args, text=True, capture_output=True)
    os.chdir(orig_dir)

    lines = result.stdout.split("\n")
    # last line of stdout contains the json output
    jsonResult = json.loads(lines[-2])
    # TODO check for the error field in jsonResult
    return jsonResult["formula"]

def robustness(spec_name, spec, cfg, outdir):
    cmd_args = ["java", "-jar", tlcian_jar, outdir, spec, cfg]
    result = subprocess.run(cmd_args, text=True, capture_output=True)
    shutil.rmtree("states/")
    #os.remove(spec_name + "_TTrace*")
    jsonResult = json.loads(result.stdout)

    assert jsonResult['comparison_type'] == 'spec_to_property'
    assert jsonResult['spec_name'] == spec_name

    diff_rep_file = jsonResult['diff_rep_file_name']
    sep_file = jsonResult['separator_file_name']
    const_value_constraint = jsonResult['const_value_constraint']
    non_const_value_constraint = run_fol_separator(outdir, sep_file)

    print("TLA+ Module: " + spec_name)
    print("Error boundary representation: " + outdir + "/" + diff_rep_file)
    print("const vc: " + const_value_constraint)
    print("non const vc: " + non_const_value_constraint)


def get_cfg(spec_name, cfg):
    if cfg is not None:
        return cfg
    return spec_name + ".cfg"

def run_robustness(args):
    # parse the cfg
    assert args.spec[-4:] == ".tla", "specs must end in .tla extension"
    spec_name = args.spec[0:-4]
    cfg = get_cfg(spec_name, args.config)
    assert cfg[-4:] == ".cfg", "configs must end in .cfg extension"
    robustness(spec_name, args.spec, cfg, args.outdir)

def run_env(args):
    print("Not supported yet")

def run_comparison(args):
    print("Not supported yet")

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
