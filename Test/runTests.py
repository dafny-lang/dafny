import os
import re
import sys
import csv
import shutil
import argparse
import operator
import platform
from enum import Enum
from time import time, strftime
from collections import defaultdict
from multiprocessing import Pool, Manager
from subprocess import Popen, call, PIPE, TimeoutExpired

# C:/Python34/python.exe runTests.py --compiler "c:/MSR/dafny/Binaries/Dafny.exe /useBaseNameForFileName /compile:1 /nologo" --difftool "C:\Program Files (x86)\Meld\Meld.exe" -j4 -f "/dprelude preludes\AlmostAllTriggers.bpl" dafny0\SeqFromArray.dfy

# c:/Python34/python.exe runTests.py --compare ../TestStable/results/SequenceAxioms/2015-06-06-00-54-52--PrettyPrinted.report.csv ../TestStable/results/SequenceAxioms/*.csv

VERBOSITY = None
KILLED = False
ANSI = False

try:
    import colorama
    no_native_ansi = os.name == 'nt' and os.environ.get("TERM") in [None, "cygwin"]
    tty = all(hasattr(stream, 'isatty') and stream.isatty() for stream in (sys.stdout, sys.stderr))
    colorama.init(strip=no_native_ansi, convert=no_native_ansi and tty)
    ANSI = True
except ImportError:
    try:
        import tendo.ansiterm
        ANSI = True
    except ImportError:
        pass

class Defaults:
    ALWAYS_EXCLUDED = ["Inputs", "Output", "sandbox", "desktop"]
    DAFNY_BIN = os.path.realpath(os.path.join(os.path.dirname(__file__), "../Binaries/Dafny.exe"))
    COMPILER = [DAFNY_BIN]
    FLAGS = ["/useBaseNameForFileName", "/compile:1", "/nologo", "/timeLimit:120"]

class Colors:
    RED = '\033[91m'
    GREEN = '\033[92m'
    YELLOW = '\033[93m'
    BRIGHT = '\033[1m'
    DIM = '\033[2m'
    RESET = '\033[0m'

class Debug(Enum):
    ERROR   = (-1, Colors.RED)
    WARNING = (-1, Colors.YELLOW)
    REPORT  = (0, Colors.RESET, True)
    INFO    = (1, Colors.RESET, True)
    DEBUG   = (2, Colors.RESET)
    TRACE   = (3, Colors.RESET)

    def __init__(self, index, color, elide=False):
        self.index = index
        self.color = color
        self.elide = elide

def wrap_color(string, color, silent=False):
    if silent:
        return " " * len(string)
    elif ANSI:
        return color + string + Colors.RESET
    else:
        return string

def debug(level, *args, **kwargs):
    kwargs["file"] = sys.stderr
    kwargs["flush"] = True

    headers = kwargs.pop("headers", [])
    if isinstance(headers, Enum):
        headers = [headers]

    silentheaders = kwargs.pop("silentheaders", False)

    if level and level.index <= VERBOSITY:
        if level:
            headers = [level] + headers

        headers = tuple(wrap_color("{: <8}".format("[" + h.name + "]"), h.color, silent = silentheaders)
                        for h in headers if not h.elide)
        print(*(headers + args), **kwargs)

class TestStatus(Enum):
    PENDING = (0, Colors.RESET)
    PASSED  = (1, Colors.GREEN)
    FAILED  = (2, Colors.RED)
    UNKNOWN = (3, Colors.RED)
    TIMEOUT = (4, Colors.RED)

    def __init__(self, index, color):
        self.index = index
        self.color = color
        self.elide = False

class Test:
    COLUMNS = ["name", "status", "start", "end", "duration", "returncodes", "suite_time", "njobs", "proc_info", "source_path", "temp_directory", "cmds", "expected", "output"]

    def __init__(self, name, source_path, cmds, timeout, compiler_id = 0):
        self.name = name
        self.dfy = None if self.name is None else (self.name + ".dfy")
        self.source_path = Test.uncygdrive(source_path)
        self.expect_path = Test.source_to_expect_path(self.source_path)
        self.source_directory, self.fname = os.path.split(self.source_path)
        self.temp_directory = os.path.join(self.source_directory, "Output")
        self.temp_output_path = os.path.join(self.temp_directory, self.fname + ".tmp")

        self.output = None
        self.expected = Test.read_normalize(self.expect_path)

        self.cmds = cmds
        self.timeout = timeout
        self.compiler_id = compiler_id
        self.cmds = [cmd.replace("%s", self.source_path) for cmd in self.cmds]
        self.cmds = [cmd.replace("%S", self.source_directory) for cmd in self.cmds]
        self.cmds = [cmd.replace("%t", self.temp_output_path) for cmd in self.cmds]
        self.cmds = [cmd.replace("%T", self.temp_directory) for cmd in self.cmds]

        self.status = TestStatus.PENDING
        self.proc_info = platform.processor()

        self.time, self.suite_time = None, None
        self.njobs, self.returncodes = None, []
        self.start, self.end, self.duration = None, None, None

    @staticmethod
    def source_to_expect_path(source):
        return source + ".expect"

    @staticmethod
    def uncygdrive(path):
        return re.sub("^/cygdrive/([a-zA-Z])/", r"\1:/", path)

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
            csv_writer.writeheader()
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
        debug(Debug.INFO, "\nTesting complete ({} test(s))".format(len(results)))

        if results:
            grouped = defaultdict(list)
            for test in results:
                grouped[test.status].append(test)

            for status, tests in sorted(grouped.items(), key=lambda x: x[0].index):
                if tests:
                    debug(Debug.REPORT, "{} of {}".format(len(tests), len(results)), headers=status)
                    if status != TestStatus.PASSED:
                        for test in tests:
                            debug(Debug.REPORT, "* " + test.dfy, headers=status, silentheaders=True)

            debug(Debug.REPORT, "Testing took {:.2f}s on {} thread(s)".format(results[0].suite_time, results[0].njobs))


    def run(self):
        debug(Debug.DEBUG, "Starting {}".format(self.dfy))
        os.makedirs(self.temp_directory, exist_ok=True)
        # os.chdir(self.source_directory)

        stdout, stderr = b'', b''
        self.start = time()

        try:
            for cmd in self.cmds:
                debug(Debug.DEBUG, "> {}".format(cmd))
                try:
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
                debug(Debug.TRACE, "Writing the output of {} to {}".format(self.dfy, self.temp_output_path))
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

    def report(self, tid, running, alltests):
        running = [alltests[rid].fname for rid in running]
        # running = ", ".join(running if len(running) <= 2 else (running[:2] + ["..."]))
        running = "; oldest thread: {}".format(wrap_color(running[0], Colors.DIM)) if running else ""

        fstring = "[{:5.2f}s] {} ({} of {}{})"
        message = fstring.format(self.duration, wrap_color(self.dfy, Colors.BRIGHT),
                                 tid, len(alltests), running)

        debug(Debug.INFO, message, headers=self.status)

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

    parser.add_argument('--compiler', type=str, action='append', default=None,
                        help='Dafny executable. Default: {}'.format(Defaults.DAFNY_BIN))

    parser.add_argument('--base-flags', type=str, action='append', default=None,
                        help='Arguments to pass to dafny. Multiple --flags are concatenated. Default: {}'.format(Defaults.FLAGS))

    parser.add_argument('--flags', '-f', type=str, action='append', default=[],
                        help='Additional arguments to pass to dafny. Useful to override some of the defaults found in --base-flags.')

    parser.add_argument('--njobs', '-j', action='store', type=int, default=None,
                        help='Number of test workers.')

    parser.add_argument('--exclude', action='append', type=str, default=[],
                        help='Excluded directories. {} are automatically added.'.format(Defaults.ALWAYS_EXCLUDED))

    parser.add_argument('--verbosity', action='store', type=int, default=1,
                        help='Set verbosity level. 0: Minimal; 1: Some info; 2: More info.')

    parser.add_argument('--report', '-r', action='store', type=str, default=None,
                        help='Give an explicit name to the report file. Defaults to the current date and time.')

    parser.add_argument('--timeout', action='store', type=float, default=15*60.0,
                        help='Prover timeout')

    parser.add_argument('--compare', action='store_true',
                        help="Compare two previously generated reports.")

    parser.add_argument('--time-all', action='store_true',
                        help="When comparing, include all timings.")

    parser.add_argument('--diff', '-d', action='store_const', const=True, default=False,
                        help="Don't run tests; show differences for one file.")

    parser.add_argument('--open', '-o', action='store_const', const=True, default=False,
                        help="Don't run tests; open one file.")

    parser.add_argument('--accept', '-a', action='store_const', const=True, default=False,
                        help="Used in conjuction with --diff, accept the new output.")

    parser.add_argument('--difftool', action='store', type=str, default="diff",
                        help='Diff program. Default: diff.')

    return parser

def run_one_internal(test, test_id, args, running):
    global KILLED
    global VERBOSITY
    VERBOSITY = args.verbosity

    if not KILLED:
        try:
            running.append(test_id)
            test.run()
        except KeyboardInterrupt:
            # There's no reliable way to handle this cleanly on Windows: if one
            # of the worker dies, it gets respawned. The reliable solution is to
            # ignore further work once you receive a kill signal
            KILLED = True
        except Exception as e:
            debug(Debug.ERROR, "[{}] {}".format(test.dfy, e))
            test.status = TestStatus.UNKNOWN
        finally:
            running.remove(test_id)

    return test

def run_one(args):
    return run_one_internal(*args)

def read_one_test(name, fname, compiler_cmds, timeout):
    for cid, compiler_cmd in enumerate(compiler_cmds):
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
                yield Test(name, source_path, cmds, timeout, cid)
            else:
                debug(Debug.DEBUG, "Test file {} has no .expect".format(fname))
        else:
            debug(Debug.INFO, "Test file {} has no RUN specification".format(fname))


def find_one(name, fname, compiler_cmds, timeout):
    name, ext = os.path.splitext(fname)
    if ext == ".dfy":
        if os.path.exists(fname):
            debug(Debug.TRACE, "Found test file: {}".format(fname))
            yield from read_one_test(name, fname, compiler_cmds, timeout)
        else:
            debug(Debug.ERROR, "Test file {} not found".format(fname))
    else:
        debug(Debug.TRACE, "Ignoring {}".format(fname))


def find_tests(paths, compiler_cmds, excluded, timeout):
    for path in paths:
        if os.path.isdir(path):
            debug(Debug.TRACE, "Searching for tests in {}".format(path))
            for base, dirnames, fnames in os.walk(path):
                dirnames[:] = [d for d in dirnames if d not in excluded]
                for fname in fnames:
                    yield from find_one(fname, os.path.join(base, fname), compiler_cmds, timeout)
        else:
            yield from find_one(path, path, compiler_cmds, timeout)


def run_tests(args):
    if args.compiler is None:
        args.compiler = Defaults.COMPILER
    if args.base_flags is None:
        args.base_flags = Defaults.FLAGS

    for compiler in args.compiler:
        if not os.path.exists(compiler):
            debug(Debug.ERROR, "Compiler not found: {}".format(compiler))
            return

    tests = list(find_tests(args.paths, [compiler + ' ' + " ".join(args.base_flags + args.flags)
                                         for compiler in args.compiler],
                            args.exclude + Defaults.ALWAYS_EXCLUDED, args.timeout))
    tests.sort(key=operator.attrgetter("name"))

    args.njobs = max(1, min(args.njobs or os.cpu_count() or 1, len(tests)))
    debug(Debug.INFO, "\nRunning {} test(s) on {} testing thread(s), timeout is {:.2f}s, started at {}".format(len(tests), args.njobs, args.timeout, strftime("%H:%M:%S")))

    try:
        pool = Pool(args.njobs)

        results = []
        start = time()
        with Manager() as manager:
            running = manager.list()
            payloads = [(t, tid, args, running) for (tid, t) in enumerate(tests)]
            for tid, test in enumerate(pool.imap_unordered(run_one, payloads, 1)):
                test.report(tid + 1, running, tests)
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
        try:
            pool.terminate()
            pool.join()
        except (FileNotFoundError, EOFError, ConnectionAbortedError):
            pass
        debug(Debug.ERROR, "Testing interrupted")


def diff(paths, accept, difftool):
    for path in paths:
        if not path.endswith(".dfy"):
            path += ".dfy"

        if not os.path.exists(path):
            debug(Debug.ERROR, "Not found: {}".format(path))
        else:
            test = Test(None, path, [], None)
            if not accept:
                call([difftool, test.expect_path, test.temp_output_path])

            if accept or input("Accept this change? (y/N) ") == "y":
                debug(Debug.INFO, path, "Accepted")
                shutil.copy(test.temp_output_path, test.expect_path)

def compare_results(globs, time_all):
    from glob import glob
    paths = [path for g in globs for path in glob(g)]
    reports = {path: Test.load_report(path) for path in paths}
    resultsets = {path: {test.dfy: (test.status, test.duration) for test in report}
                  for path, report in reports.items()}

    all_tests = set(name for resultset in resultsets.values() for name in resultset.keys())

    reference = resultsets[paths[0]]
    for path, resultset in resultsets.items():
        resultset["$$TOTAL$$"] = None, sum(v[1] for v in resultset.values() if v[1] and v[0] != TestStatus.TIMEOUT)

    with open("compare.csv", mode='w', newline='') as writer:
        csv_writer = csv.writer(writer, dialect='excel')
        csv_writer.writerow(["Name"] + [os.path.split(path)[1].lstrip("0123456789-") for path in paths])

        for name in sorted(all_tests) + ["$$TOTAL$$"]:
            ref_status, ref_duration = reference[name]

            row = []
            row.append(name)
            row.append(ref_duration)
            for path in paths[1:]:
                res = resultsets[path].get(name)
                test_status, test_duration = res if res else (TestStatus.UNKNOWN, None)
                if res is not None and (test_status == ref_status or time_all):
                    result = "{:.2%}".format((test_duration - ref_duration) / ref_duration)
                else:
                    result = test_status.name + "?!"
                row.append(result)

            csv_writer.writerow(row)

def main():
    global VERBOSITY
    parser = setup_parser()
    args = parser.parse_args()
    VERBOSITY = args.verbosity

    if os.name != 'nt' and os.environ.get("TERM") == "cygwin":
        debug(Debug.WARNING, "If you run into issues, try using Windows' Python instead of Cygwin's")

    if args.diff:
        diff(args.paths, args.accept, args.difftool)
    elif args.open:
        os.startfile(args.paths[0])
    elif args.compare:
        compare_results(args.paths, args.time_all)
    else:
        run_tests(args)

if __name__ == '__main__':
    main()
