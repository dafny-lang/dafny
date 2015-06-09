import os
import re
import sys
import csv
import shlex
import shutil
import argparse
import operator
import platform
from enum import Enum
from time import time, strftime
from multiprocessing import Pool
from collections import defaultdict
from subprocess import Popen, call, PIPE, TimeoutExpired

# C:/Python34/python.exe runTests.py --compiler "c:/MSR/dafny/Binaries/Dafny.exe /useBaseNameForFileName /compile:1 /nologo" --difftool "C:\Program Files (x86)\Meld\Meld.exe" -j4 -f "/dprelude preludes\AlmostAllTriggers.bpl" dafny0\SeqFromArray.dfy

# c:/Python34/python.exe runTests.py --compare ../TestStable/results/SequenceAxioms/2015-06-06-00-54-52--PrettyPrinted.report.csv ../TestStable/results/SequenceAxioms/*.csv

ANSI = False
try:
    import colorama
    colorama.init()
    ANSI = True
except ImportError:
    try:
        import tendo.ansiterm
        ANSI = True
    except ImportError:
        pass

VERBOSITY = None
KILLED = False

ALWAYS_EXCLUDED = ["Output", "snapshots", "sandbox"]


class Debug(Enum):
    ERROR  = (-1, '\033[91m')
    REPORT = (0, '\033[0m')
    INFO   = (1, '\033[0m')
    DEBUG  = (2, '\033[0m')
    TRACE  = (3, '\033[0m')

    def __init__(self, index, color):
        self.index = index
        self.color = color

def wrap_color(string, color):
    if ANSI:
        return color + string + '\033[0m'
    else:
        return string

def debug(level, *args, **kwargs):
    kwargs["file"] = sys.stderr
    kwargs["flush"] = True

    headers = kwargs.pop("headers", [])
    if isinstance(headers, Enum):
        headers = [headers]

    if level and level.index <= VERBOSITY:
        if level:
           headers = [level] + headers
        headers = tuple("[" + wrap_color("{: ^8}".format(h.name), h.color) + "]" for h in headers)
        print(*(headers + args), **kwargs)

class TestStatus(Enum):
    PENDING = (0, '\033[0m')
    PASSED  = (1, '\033[92m')
    FAILED  = (2, '\033[91m')
    UNKNOWN = (3, '\033[91m')
    TIMEOUT = (4, '\033[91m')

    def __init__(self, index, color):
        self.index = index
        self.color = color

class Test:
    COLUMNS = ["name", "status", "start", "end", "duration", "returncodes", "suite_time", "njobs", "proc_info", "source_path", "temp_directory", "cmds", "expected", "output"]

    def __init__(self, name, source_path, cmds, timeout):
        self.name = name
        self.source_path = source_path
        self.expect_path = Test.source_to_expect_path(self.source_path)
        self.source_directory, self.fname = os.path.split(self.source_path)
        self.temp_directory = os.path.join(self.source_directory, "Output")
        self.temp_output_path = os.path.join(self.temp_directory, self.fname + ".tmp")

        self.output = None
        self.expected = Test.read_normalize(self.expect_path)

        self.cmds = cmds
        self.timeout = timeout
        self.cmds = [cmd.replace("%s", self.source_path) for cmd in self.cmds]
        self.cmds = [cmd.replace("%t", self.temp_output_path) for cmd in self.cmds]

        self.status = TestStatus.PENDING
        self.proc_info = platform.processor()

        self.time, self.suite_time = None, None
        self.njobs, self.returncodes = None, []

    @staticmethod
    def source_to_expect_path(source):
        return source + ".expect"

    @staticmethod
    def read_normalize(path):
        with open(path, mode="rb") as reader:
            return reader.read().replace(b'\r\n', b'\n').replace(b'\r', b'\n')

    @staticmethod
    def build_report(tests, name):
        time = strftime("%Y-%m-%d-%H-%M-%S")
        if name:
            directory, fname = os.path.split(name)
            name = os.path.join(directory, time + "--" + fname)
        else:
            name = time

        with open(name + ".csv", mode='w', newline='') as writer:
            csv_writer = csv.DictWriter(writer, Test.COLUMNS, dialect='excel')
            csv_writer.writeheader()  # TODO enable later
            for test in tests:
                test.serialize(csv_writer)

    @staticmethod
    def load_report(path):
        results = []
        with open(path) as csvfile:
            for row in csv.DictReader(csvfile):  #, fieldnames=Test.COLUMNS):
                results.append(Test.deserialize(row))
        return results

    @staticmethod
    def summarize(results):
        debug(None, "")
        debug(Debug.INFO, "** Testing complete ({} tests) **".format(len(results)))

        if results:
            debug(Debug.REPORT, "Testing took {:.2f}s on {} threads".format(results[0].suite_time, results[0].njobs))

            grouped = defaultdict(list)
            for t in results:
                grouped[t.status].append(t)

            for status, ts in sorted(grouped.items(), key=lambda x: x[0].index):
                if ts:
                    debug(Debug.REPORT, "{}/{} -- {}".format(len(ts), len(results), ", ".join(t.name for t in ts)), headers=status)

    def run(self):
        debug(Debug.DEBUG, "Starting {}".format(self.name))
        os.makedirs(self.temp_directory, exist_ok = True)
        # os.chdir(self.source_directory)

        stdout, stderr = b'', b''
        self.start = time()

        try:
            for cmd in self.cmds:
                debug(Debug.DEBUG, "> {}".format(cmd))
                try:
                    #, timeout = 60*60)
                    proc = Popen(cmd, stdin=PIPE, stdout=PIPE, stderr=PIPE, shell=True)
                    _stdout, _stderr = proc.communicate(timeout=self.timeout)
                    stdout, stderr = stdout + _stdout, stderr + _stderr
                    self.returncodes.append(proc.returncode)
                except FileNotFoundError:
                    debug(Debug.ERROR, "Program '{}' not found".format(cmd))
                    self.status = TestStatus.UNKNOWN
                    return
                except TimeoutExpired:
                    self.status = TestStatus.TIMEOUT
                    self.end = self.start + self.timeout
                    self.duration = self.timeout
                    return

            self.end = time()
            self.duration = self.end - self.start

            stdout, stderr = stdout.strip(), stderr.strip()
            if stdout != b"" or stderr != b"":
                debug(Debug.TRACE, "Writing the output of {} to {}".format(self.name, self.temp_output_path))
                with open(self.temp_output_path, mode='ab') as writer:
                    writer.write(stdout + stderr)
            if stderr != b"":
                debug(Debug.TRACE, stderr)

            self.update_status()
        except TimeoutExpired:
            self.status = TestStatus.TIMEOUT
        except KeyboardInterrupt:
            raise

    def update_status(self):
        self.output = Test.read_normalize(self.temp_output_path)
        self.status = TestStatus.PASSED if self.expected == self.output else TestStatus.FAILED

    def report(self, tid):
        debug(Debug.INFO, "{} ({})".format(self.name, tid), headers=self.status)

    @staticmethod
    def write_bytes(base_directory, relative_path, extension, contents):
        with open(os.path.join(base_directory, relative_path + extension), mode='wb') as writer:
            writer.write(contents)

    def serialize(self, csv_writer):
        csv_writer.writerow({col: getattr(self, col) for col in Test.COLUMNS})

    @classmethod
    def deserialize(cls, row):
        test = cls.__new__(cls)
        for col, val in row.items():
            setattr(test, col, val)
        test.duration = float(test.duration)
        test.status = next(x for x in TestStatus if str(x) == test.status)
        return test

def setup_parser():
    parser = argparse.ArgumentParser(description='Run the Dafny test suite.')

    parser.add_argument('paths', type=str, action='store', nargs='+',
                        help='Input files or folders. Folders are searched for .dfy files.')

    parser.add_argument('--compiler', type=str, action='store', default='Dafny.exe',
                        help='Command to use for %dafny.')

    parser.add_argument('--more-flags', '-f', type=str, action='store', default='',
                        help='Command used to run the tests.')

    parser.add_argument('--njobs', '-j', action='store', type=int, default=None,
                        help='Number of test workers.')

    parser.add_argument('--exclude', action='append', type=str, default=[],
                        help='Excluded directories. {} are automatically added.'.format(ALWAYS_EXCLUDED))

    parser.add_argument('--verbosity', action='store', type=int, default=1,
                        help='Set verbosity level. 0: Minimal; 1: Some info; 2: More info.')

    parser.add_argument('--report', '-r', action='store', type=str, default=None,
                        help='Give an explicit name to the report file. Defaults to the current date and time.')

    parser.add_argument('--timeout', action='store', type=float, default=15*60.0,
                        help='Prover timeout')

    parser.add_argument('--compare', action='store_true',
                        help="Compare two previously generated reports.")

    parser.add_argument('--diff', '-d', action='store_const', const=True, default=False,
                        help="Don't run tests; show differences for one file.")

    parser.add_argument('--open', '-o', action='store_const', const=True, default=False,
                        help="Don't run tests; open one file.")

    parser.add_argument('--accept', '-a', action='store_const', const=True, default=False,
                        help="Used in conjuction with --diff, accept the new output.")

    parser.add_argument('--difftool', action='store', type=str, default="diff",
                        help='Diff command line.')
    return parser


def run_one(test_args):
    global KILLED
    global VERBOSITY

    test, args = test_args
    VERBOSITY = args.verbosity

    try:
        if not KILLED:
            test.run()
    except KeyboardInterrupt:
        # There's no reliable way to handle this cleanly on Windows: if one
        # of the worker dies, it gets respawned. The reliable solution is to
        # ignore further work once you receive a kill signal
        KILLED = True
    except Exception as e:
        debug(Debug.ERROR, "For file {}".format(test.name), e)
        test.status = TestStatus.UNKNOWN
    return test

def read_one_test(name, fname, compiler_cmd, timeout):
    source_path = os.path.realpath(fname)
    with open(source_path, mode='r') as reader:
        cmds = []
        for line in reader:
            line = line.strip()
            match = re.match("^// *RUN: *(?!%diff)([^ ].*)$", line)
            if match:
                cmds.append(match.groups()[0].replace("%dafny", compiler_cmd))
            else:
                break
    if cmds:
        if os.path.exists(Test.source_to_expect_path(source_path)):
            return [Test(name, source_path, cmds, timeout)]
        else:
            debug(Debug.DEBUG, "Test file {} has no .expect".format(fname))
    else:
        debug(Debug.INFO, "Test file {} has no RUN specification".format(fname))

    return []


def find_one(name, fname, compiler_cmd, timeout):
    name, ext = os.path.splitext(fname)
    if ext == ".dfy":
        if os.path.exists(fname):
            debug(Debug.TRACE, "Found test file: {}".format(fname))
            yield from read_one_test(name, fname, compiler_cmd, timeout)
        else:
            debug(Debug.ERROR, "Test file {} not found".format(fname))
    else:
        debug(Debug.TRACE, "Ignoring {}".format(fname))


def find_tests(paths, compiler_cmd, excluded, timeout):
    for path in paths:
        if os.path.isdir(path):
            debug(Debug.TRACE, "Searching for tests in {}".format(path))
            for base, dirnames, fnames in os.walk(path):
                dirnames[:] = [d for d in dirnames if d not in excluded]
                for fname in fnames:
                    yield from find_one(fname, os.path.join(base, fname), compiler_cmd, timeout)
        else:
            yield from find_one(path, path, compiler_cmd, timeout)


def run_tests(args):
    compiler_cmd = shlex.split(args.compiler)
    compiler_bin = compiler_cmd[0]

    if not os.path.exists(compiler_cmd[0]):
        debug(Debug.ERROR, "Compiler not found: {}".format(compiler_bin))
        return

    tests = list(find_tests(args.paths, args.compiler + ' ' + args.more_flags,
                            args.exclude + ALWAYS_EXCLUDED, args.timeout))
    tests.sort(key=operator.attrgetter("name"))

    args.njobs = args.njobs or os.cpu_count() or 1
    debug(Debug.INFO, "** Running {} tests on {} testing threads, timeout is {:.2f} **".format(len(tests), args.njobs, args.timeout))
    try:
        pool = Pool(args.njobs) #, init_tester)

        start = time()
        results = []
        for tid, test in enumerate(pool.imap_unordered(run_one, [(t, args) for t in tests], 1)):
            test.report(tid + 1)
            results.append(test)
        pool.close()
        pool.join()
        suite_time = time() - start

        for t in results:
            t.njobs = args.njobs
            t.suite_time = suite_time

        Test.summarize(results)
        Test.build_report(results, args.report)
    except KeyboardInterrupt:
        pool.terminate()
        pool.join()
        debug(Debug.ERROR, "Testing interrupted")


def diff(paths, accept, difftool):
    if len(paths) > 1:
        debug(Debug.ERROR, "Please specify a single path")
    elif not os.path.exists(paths[0]):
        debug(Debug.ERROR, "Not found: {}".format(paths[0]))
    else:
        test = Test(None, paths[0], [], None)
        if accept:
            shutil.copy(test.temp_output_path, test.expect_path)
        else:
            call([difftool, test.expect_path, test.temp_output_path])

def compare_results(globs):
    from glob import glob
    paths = [path for g in globs for path in glob(g)]
    reports = {path: Test.load_report(path) for path in paths}
    resultsets = {path: {test.name: (test.status, test.duration) for test in report}
                  for path, report in reports.items()}

    all_tests = set(name for resultset in resultsets.values() for name in resultset.keys())

    reference = resultsets[paths[0]]
    for path, resultset in resultsets.items():
        resultset["$$TOTAL$$"] = None, sum(v[1] for v in resultset.values() if v[1] and v[0] != TestStatus.TIMEOUT)

    print(all_tests)
    with open("compare.csv", mode='w', newline='') as writer:
        csv_writer = csv.writer(writer, dialect='excel')
        csv_writer.writerow(["Name"] + [os.path.split(path)[1].lstrip("0123456789-") for path in paths])

        for name in sorted(all_tests) + ["$$TOTAL$$"]:
            ref_status, ref_duration = reference[name]

            row = []
            row.append(name)
            row.append(ref_duration)
            for path in paths[1:]:
                test_status, test_duration = resultsets[path][name]
                if test_status == ref_status:
                    result = "{:.2%}".format((test_duration - ref_duration) / ref_duration)
                else:
                    result = test_status.name + "?!"
                row.append(result)

            csv_writer.writerow(row)


# def compare_results(globs):
#     from glob import glob
#     baseline = dict()
#     results = defaultdict(dict)
#     paths = [p for g in globs for p in glob(g)]

#     for path in paths:
#         report = Test.load_report(path)
#         for test in report:  # FIXME add return codes (once we have them)
#             if test.duration:
#                 bl = baseline.setdefault(test.name, float(test.duration))
#                 result = "timeout" if test.status == TestStatus.TIMEOUT else (float(test.duration) - bl) / bl
#             else:
#                 result = "???"
#             results[test.name][path] = result, test.duration, test.status.name

#     with open("compare.csv", mode='w', newline='') as writer:
#         csv_writer = csv.writer(writer, dialect='excel')
#         csv_writer.writerow(["Name"] + [os.path.split(path)[1].lstrip("0123456789-") for path in paths])
#         for name, tresults in sorted(results.items()):
#             res = [tresults.get(path) for path in paths]
#             csv_writer.writerow([name] + [r[0] for r in res])
#             csv_writer.writerow([name + "*"] + [r[1:] for r in res])


def main():
    global VERBOSITY
    parser = setup_parser()
    args = parser.parse_args()
    VERBOSITY = args.verbosity

    if args.diff:
        diff(args.paths, args.accept, args.difftool)
    elif args.open:
        os.startfile(args.paths[0])
    elif args.compare:
        compare_results(args.paths)
    else:
        run_tests(args)

if __name__ == '__main__':
    main()
