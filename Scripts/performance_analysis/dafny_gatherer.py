#!/usr/bin/env python3
from math import ceil
from os import listdir, extsep
from os.path import isfile, join, basename, dirname
from subprocess import CalledProcessError, run, DEVNULL
import csv
import uuid
from dataclasses import dataclass, asdict, field
from multiprocessing import Pool
from re import search
import argparse

@dataclass
class Z3_Stats:
    added_eqs: int = 0
    arith_assert_diseq: int = 0
    arith_assert_lower: int = 0
    arith_assert_upper: int = 0
    arith_assume_eqs: int = 0
    arith_bound_prop: int = 0
    arith_branch_var: int = 0
    arith_conflicts: int = 0
    arith_eq_adapter: int = 0
    arith_fixed_eqs: int = 0
    arith_gcd_conflicts: int = 0
    arith_gcd_tests: int = 0
    arith_gomory_cuts: int = 0
    arith_grobner: int = 0
    arith_ineq_splits: int = 0
    arith_max_min: int = 0
    arith_nonlinear_bounds: int = 0
    arith_nonlinear_horner: int = 0
    arith_num_rows: int = 0
    arith_offset_eqs: int = 0
    arith_patches: int = 0
    arith_patches_succ: int = 0
    arith_pivots: int = 0
    arith_pseudo_nonlinear: int = 0
    arith_row_summations: int = 0
    arith_tableau_max_columns: int = 0
    arith_tableau_max_rows: int = 0
    array_def_const: int = 0
    array_ax1: int = 0
    array_ax2: int = 0
    array_def_const: int = 0
    array_def_store: int = 0
    array_exp_ax2: int = 0
    array_ext_ax: int = 0
    array_sel_as_array: int = 0
    array_sel_const: int = 0
    array_splits: int = 0
    bv_bit2core: int = 0
    bv_core_eq: int = 0
    bv_diseqs: int = 0
    bv_dynamic_diseqs: int = 0
    bv_dynamic_eqs: int = 0
    conflicts: int = 0
    crash: bool = False
    decisions: int = 0
    del_clause: int = 0
    dyn_ack: int = 0
    final_checks: int = 0
    interface_eqs: int = 0
    lazy_quant_instantiations: int = 0
    max_generation: int = 0
    max_memory: float = 0.0
    max_missed_qa_cost: float = 0.0
    min_missed_qa_cost: float = 0.0
    minimized_lits: int = 0
    missed_quant_instantiations: int = 0
    memory: float = 0.0
    mk_bool_var: int = 0
    mk_clause: int = 0
    num_allocs: int = 0
    num_checks: int = 0
    propagations: int = 0
    quant_instantiations: int = 0
    restarts: int = 0
    rlimit: int = 0
    rlimit_count: int = 0
    time: float = 0.0
    timeout: bool = False
    total_time: float = 0.0
    qi_unique_quants: int = 0
    qi: int = 0
    qi_dummys: int = 0
    qi_top: int = 0
    qi_top_names: list = field(default_factory=lambda: [])
    qi_dummy_top: int = 0

@dataclass
class Profiler_Stats:
    enodes: int = 0
    given_equalities: int = 0
    trans_equalities: int = 0
    instantiations: int = 0
    mbqi_instantiations: int = 0
    theory_solving_instantiations: int = 0
    axioms_instantiations: int = 0
    quantifiers_instantiations: int = 0
    nodes: int = 0
    p_crash: bool = False

def parse_number(s):
    try:
        return int(s)
    except:
        try:
            return float(s)
        except Exception as e:
            raise e


def parse_z3_stats(out, err):
    d = dict()
    quants = dict()
    if out[0:7] == "timeout":
        d["timeout"] = True
    for l in out.splitlines():
        colon = l.find(':')
        if colon < 0 or l.startswith("declared"):
            continue
        tokens = l[colon+1:].replace(')', '').split()
        if not tokens or tokens[0] in ["unknown", "reason-unknown", "model", "invalid", "unexpected"]:
            continue
        try:
            d[tokens[0].replace('-', '_').replace('>', '')] = parse_number(tokens[1])
        except Exception as e:
            print(l)
            raise e
    for l in err.splitlines():
        if not l.startswith("[quantifier_instances]"):
            continue
        s = l.removeprefix("[quantifier_instances]")
        indices = [i for i, c in enumerate(s) if c == ':']
        if len(indices) < 5:
            continue
        aftername = indices[-5]
        if aftername < 0:
            continue
        name = s[:aftername].strip()
        stats = [stat.strip() for stat in s[aftername+3:].split(':')]
        if len(stats) != 5:
            print(s)
            print(stats)
        # Instances that are unsat and those that are sat
        try:
            quants[name] = (int(stats[0]), int(stats[2]))
        except Exception as e:
            print(l)
            raise e 
    assert set(d.keys()) <= set(Z3_Stats.__dataclass_fields__.keys()), "Unknown stats: " + str(list(map(lambda k: f"{k}: {d[k]}", set(d.keys()) - set(Z3_Stats.__dataclass_fields__.keys()))))
    stats = Z3_Stats(**d)
    insts = [quant[0] for quant in quants.values()]
    dummies = [quant[1] for quant in quants.values()]
    stats.qi_unique_quants = len(insts)
    stats.qi = sum(insts)
    stats.qi_dummys = sum(dummies)
    def top_percent(p, l):
        return sum(sorted(l)[-(ceil(float(len(l))*p)):])
    stats.qi_top = top_percent(0.02, insts)
    items = list(map(lambda i: (i[0], i[1][0]), quants.items()))
    items.sort(key=lambda e: e[1])
    stats.qi_top_names = items # [-5:]
    stats.qi_dummy_top = top_percent(0.02, dummies)
    return stats

def parse_profiler_stats(s):
    d = dict()
    for l in s.splitlines():
        if l.count(':') != 1 or l.count('=') > 0:
            continue
        tokens = l.split(": ")
        try:
            d[tokens[0].replace("no-","").replace("-count", "").replace('-', '_')] = parse_number(tokens[1])
        except:
            print("Failed parsing SMTscope output:")
            print(s)
    return Profiler_Stats(**d)

def analyse_file(f, config):
    Z3_Log = join(config.result_dir, str(uuid.uuid4()))
    try:
        r = run([config.z3_path,
                "nlsat.seed=" + str(config.seed),
                "sls.random_seed=" + str(config.seed),
                "fp.spacer.random_seed=" + str(config.seed),
                "smt.random_seed=" + str(config.seed),
                "sat.random_seed=" + str(config.seed),
                "trace=true",
                "proof=true",
                "trace_file_name=" + Z3_Log,
                "-st",
                "smt.qi.profile=true",
                "-T:" + str(config.timeout),
                join(join(config.result_dir, "smt2"), f)],
                capture_output=True)
        
        if r.returncode != 0 and not search(r"\(error \"line [0-9]* column [0-9]*: model is not available\"\)\n", r.stdout.decode()):
            raise CalledProcessError(r.returncode, r.args, r.stdout)
        
        z3_stats = parse_z3_stats(r.stdout.decode(), r.stderr.decode())
        r = run([config.smt_scope_path, "stats", Z3_Log], capture_output=True, check=True)
        profiler_stats = parse_profiler_stats(r.stdout.decode())
    except CalledProcessError as e:
        profiler_stats = Profiler_Stats()
        if 'z3_stats' not in locals():
            z3_stats = Z3_Stats()
        if "\ntimeout\n" in e.stdout.decode():
            z3_stats.timeout = True
        else:
            if "stats" in e.cmd:
                profiler_stats.p_crash = True
            else:
                z3_stats.crash = True
            print(f"Running {' '.join(e.cmd)} failed")
            print(e.stdout)
            print(e.stderr)
    except Exception as e:
        print(f"Failure while analysing {f}")
        print(e)
        raise e
    finally:
        run(["rm", Z3_Log])

    # assert z3_stats.quant_instantiations == profiler_stats.quantifiers_instantiations, f"Z3 reports {z3_stats.quant_instantiations} qi's, while the analyser finds {profiler_stats.quantifiers_instantiations}"
    
    d = asdict(z3_stats) | asdict(profiler_stats)
    d["filename"] = f
    return(d)

def generate_bpl(line, config):
    line = line.rstrip()
    parts = line.split(" ")
    filename = parts[0]
    run([config.dafny_path,
         "/compile:0",
         "/noVerify",
         "/print:" + join(join(config.result_dir, "bpl"), filename.split(extsep, 1)[0].replace('/', '_') + ".bpl")] +
         parts[1:] +
         [join(config.result_dir, filename)],
         stdout=DEVNULL,
         stderr=DEVNULL)

def generate_smt2(f, config):
    boogiefile = join(join(config.result_dir, "bpl"), f)
    extraargs = []
    with open(boogiefile) as input_file:
        header = [next(input_file) for _ in range(2)]
        if len(header) != 2:
            return
        assert header[0].startswith("// dafny")
        OPTIONS = "// Command Line Options:"
        assert header[1].startswith(OPTIONS)
        extraargs = [o for o in header[1][len(OPTIONS)+1:-1].split(' ') if "vcsSplitOnEveryAssert" in o or "proverOpt" in o or "typeEncoding" in o]
    
    run([config.boogie_path,
         "/proverOpt:SOLVER=noop",
         "/infer:j",
         "/proverOpt:O:auto_config=false",
         "/proverOpt:O:type_check=true",
         "/proverOpt:O:smt.case_split=3",
         "/proverOpt:O:smt.qi.eager_threshold=44",
         "/proverOpt:O:smt.qi.lazy_threshold=44",
         "/proverOpt:O:smt.delay_units=true",
         "/proverOpt:O:smt.arith.solver=2",
         "/proverLog:" + join(config.result_dir, "smt2") + "/@PROC@.smt2",
         boogiefile] + extraargs,
         stdout=DEVNULL,
         stderr=DEVNULL)

def process_snapshot(config):
    """Process a Dafny snapshot and generate statistics"""
    # Create result directory structure
    run(["rm", "-R", config.result_dir], stderr=DEVNULL, stdout=DEVNULL)
    run(["mkdir", config.result_dir])
    run(["tar", "-xf", config.snapshot_path, "-C", config.result_dir])
    run(["mkdir", join(config.result_dir, "bpl")])
    run(["mkdir", join(config.result_dir, "smt2")])

    # Generate BPL files
    with open(join(config.result_dir, "dfy-list"), 'r') as dfylist:
        lines = [line.rstrip() for line in dfylist]
        with Pool(config.pool_size) as p:
            results = p.starmap(generate_bpl, [(line, config) for line in lines], config.chunksize)

    # Generate SMT2 files
    bpls = [f for f in listdir(join(config.result_dir, "bpl"))
            if isfile(join(join(config.result_dir, "bpl"), f)) and "bpl" in f]
    with Pool(config.pool_size) as p:
        results = p.starmap(generate_smt2, [(bpl, config) for bpl in bpls], config.chunksize)

    # Analyze files and write results to CSV
    output_csv = join(dirname(config.result_dir), basename(config.result_dir) + ".csv")
    with open(output_csv, 'w', newline='') as csvfile:
        fieldnames = ["filename"] + list(Z3_Stats.__dataclass_fields__.keys()) + list(Profiler_Stats.__dataclass_fields__.keys())
        writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
        writer.writeheader()

        files = [f for f in listdir(join(config.result_dir, "smt2"))
                if isfile(join(join(config.result_dir, "smt2"), f)) and "smt2" in f]
        files.sort()

        with Pool(config.pool_size) as p:
            results = p.starmap(analyse_file, [(f, config) for f in files], config.chunksize)

        writer.writerows(results)

    # Clean up if requested
    if config.cleanup:
        run(["rm", "-R", config.result_dir])
    
    print(f"Analysis complete. Results written to {output_csv}")
    return output_csv

def main():
    parser = argparse.ArgumentParser(
        description="Process Dafny snapshots and generate statistics",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter
    )
    
    # Required arguments
    parser.add_argument("snapshot_path",
                        help="Path to the Dafny snapshot archive (.tar)")
    
    # Optional arguments with defaults
    parser.add_argument("--seed", type=int, default=1,
                        help="Random seed for Z3")
    parser.add_argument("--working-dir", default="/tmp/",
                        help="Working directory for temporary files")
    parser.add_argument("--pool-size", type=int, default=1,
                        help="Size of the process pool for parallel execution")
    parser.add_argument("--timeout", type=int, default=300,
                        help="Timeout in seconds for Z3")
    parser.add_argument("--z3-path", default="z3",
                        help="Path to Z3 executable")
    parser.add_argument("--smt-scope-path", default="smt-scope",
                        help="Path to SMTscope executable")
    parser.add_argument("--dafny-path", default="dafny",
                        help="Path to Dafny executable")
    parser.add_argument("--boogie-path", default="boogie",
                        help="Path to Boogie executable")
    parser.add_argument("--no-cleanup", action="store_false", dest="cleanup",
                        help="Do not remove temporary files after processing")
    parser.add_argument("--chunksize", type=int, default=1,
                        help="Chunksize for parallel processing")
    
    args = parser.parse_args()
    
    # Set up the result directory based on the snapshot name
    args.result_dir = join(args.working_dir, basename(args.snapshot_path).split(extsep, 1)[0])
    
    # Process the snapshot
    output_csv = process_snapshot(args)

if __name__ == "__main__":
    main()
