#!/usr/bin/env python3
"""Differential tester for Dafny.

This takes a sequence of snapshots and verifies them through Dafny's CLI as well
as through Dafny's LSP server.  The results are matched for equality.

Limitations:

- This only checks error messages, not return codes

- This only checks for errors in one "main" file, not in all files reported by
  the LSP server.
"""

from typing import Any, Dict, Iterable, List, Tuple, TypeVar

import json
import os
import platform
import re
import shlex
import shutil
import subprocess
import sys

from collections import deque
from pathlib import Path
from subprocess import PIPE

# For ordered dicts and f strings
assert sys.version_info >= (3, 7)

T = TypeVar("T")

Snapshot = str
"""The contents of a Dafny file."""

LSPMessage = Dict[str, Any]
"""A single LSP client request."""

VerificationResult = List[str]
"""Structured output returned by Dafny."""

FIXME = NotImplementedError
DEBUG = False
TEE = "inputs.log"

def which(exe):
    """Locate executable `exe`; raise a ``ValueError`` if it can't be found."""
    if isinstance(exe, list):
        return [which(exe[0]), *exe[1:]]
    path = shutil.which(exe)
    if path is None:
        raise ValueError(f"Executable not found in PATH: {exe}")
    return path


def debug(prefix, *msgs, **kwds):
    """Print `msgs` with `prefix`; forward `kwds` to `print`."""
    if DEBUG:
        print(prefix, *msgs, **{**kwds, "file": sys.stderr})


def _no_window():
    """Create a startupinfo object.

    On Windows, set it up to run without showing a command window.
    """
    si = subprocess.STARTUPINFO()
    if platform.system() == "Windows":
        si.dwFlags |= subprocess.STARTF_USESHOWWINDOW
    return si


class Tee(object):
    def __init__(self, *streams):
        self.streams = streams
    def close(self):
        for s in self.streams:
            s.close()
    def write(self, data):
        for s in self.streams:
            s.write(data)
    def flush(self):
        for s in self.streams:
            s.flush()


class ProverInputs:
    """A sequence of inputs to Dafny."""

    def as_lsp(self) -> "LSPTrace":
        """Convert self into an LSP trace."""
        raise NotImplementedError

    def as_snapshots(self) -> "Snapshots":
        """Convert self into a sequence of snapshots."""
        raise NotImplementedError

    def __len__(self):
        raise NotImplementedError

class ProverOutput:
    """An output of Dafny."""

    # @property
    # def errors(self) -> List[VerificationResult]:
    #     """Normalize this output and convert it to a list of results."""
    #     raise NotImplementedError

    # Strings are easier to diff than structured data, especially when looking
    # at insertions/deletions.
    def format(self) -> str:
        raise NotImplementedError

class LSPMethods:
    """Global constants for LSP Methods."""
    didOpen = "textDocument/didOpen"
    didChange = "textDocument/didChange"
    publishDiagnostics = "textDocument/publishDiagnostics"
    NEED_DIAGNOSTICS = {didOpen, didChange}


class LSPTrace(ProverInputs):
    """A sequence of messages sent by an LSP client."""

    def __init__(self, commands: Iterable[LSPMessage]):
        self.messages: List[LSPMessage] = list(commands)

    @classmethod
    def from_json(cls, js: bytes) -> "LSPTrace":
        """Load an LSP trace from an encoded `js` string."""
        return LSPTrace(json.loads(js))

    def as_lsp(self) -> "LSPTrace":
        """Convert self into an LSP trace."""
        return self

    def _iter_snapshots(self) -> Iterable[Snapshot]:
        for msg in self.messages:
            if msg["method"] == LSPMethods.didOpen:
                yield msg["params"]["textDocument"]["text"]
            if msg["method"] == LSPMethods.didChange:
                for change in msg["params"]["contentChanges"]:
                    yield change["text"]  # FIXME add support for ranges

    @property
    def uri(self):
        """Return the current document's URI."""
        for m in self.messages:
            if m["method"] == LSPMethods.didOpen:
                return m["textDocument"]["uri"]
        raise ValueError("No didOpen message found in LSP trace.")

    def as_snapshots(self) -> "Snapshots":
        """Convert self into a sequence of snapshots."""
        return Snapshots(self.uri, self._iter_snapshots())

    def __len__(self):
        return sum(msg["method"] in (LSPMethods.didOpen, LSPMethods.didChange)
                   for msg in self.messages)


class Snapshots:
    """A sequence of Dafny files."""

    VERNUM_RE = re.compile(r"\A(?P<stem>.*)[.]v(?P<num>[0-9]+)\Z")

    def __init__(self, uri: str, snapshots: Iterable[Snapshot]):
        self.uri = uri
        self.snapshots = list(snapshots)

    @classmethod
    def _find_snapshots(cls, name: str) -> Iterable[Tuple[int, Path]]:
        """Yield paths matching stem.vN.suffix when `name` is stem.suffix."""
        ref = Path(name)
        for f in ref.parent.iterdir():
            if ref.suffix == f.suffix:
                mnum = cls.VERNUM_RE.match(f.stem)
                if mnum and ref.stem == mnum.group("stem"):
                    yield int(mnum.group("num")), f

    @classmethod
    def from_files(cls, name: str) -> "Snapshots":
        """Read files matching stem.vN.suffix when `name` is stem.suffix."""
        uri = Path(name).absolute().as_uri()
        files = (f for _, f in sorted(cls._find_snapshots(name)))
        snaps = (f.read_text("utf-8") for f in files)
        return Snapshots(uri, snaps)

    @classmethod
    def _complete_range(cls, previous: Snapshot):
        last_line = previous.count("\n")
        last_bol = previous.rfind("\n") + 1
        last_pos = len(previous[last_bol:].encode("utf-16le"))
        return {"start": {"line": 0, "character": 0},
                "end": {"line": last_line, "character": last_pos}}

    @classmethod
    def _lsp_of_snapshot(cls, uri: str, version: int,
                         snapshot: Snapshot, previous: Snapshot):
        document = {"uri": uri, "languageId": "dafny", "version": version}
        return {
            "method": LSPMethods.didOpen,
            "params": {"textDocument": {**document, "text": snapshot}}
        } if previous is None else {
            "method": LSPMethods.didChange,
            "params": {"textDocument": document,
                       "contentChanges": [{
                           "text": snapshot,
                           "range": cls._complete_range(previous)
                       }]}
        }

    def _iter_lsp(self) -> Iterable[LSPMessage]:
        yield {
            "method": "initialize",
            "params": {"processId": os.getpid(),
                       "clientInfo": {"name": "Dafny diff tester"},
                       "rootUri": Path(os.getcwd()).as_uri(),
                       "capabilities": {"publishDiagnostics": {}}}
        }
        yield {"method": "initialized", "params": {}}
        prev = None
        for version, snap in enumerate(self.snapshots):
            yield self._lsp_of_snapshot(self.uri, version, snap, prev)
            prev = snap
        yield {"method": "shutdown", "params": {}}
        yield {"method": "exit", "params": {}}

    def _iter_jrpc(self) -> Iterable[LSPMessage]:
        METHODS = {"initialize", "shutdown"}
        for id, msg in enumerate(self._iter_lsp()):
            idd = {"id": id} if msg["method"] in METHODS else {}
            yield {"jsonrpc": "2.0", **msg, **idd}

    def as_lsp(self) -> "LSPTrace":
        """Convert self into an LSP trace."""
        return LSPTrace(self._iter_jrpc())

    def as_snapshots(self) -> "Snapshots":
        """Convert self into a sequence of snapshots."""
        return self

    def __len__(self):
        return len(self.snapshots)

class Driver:
    """Abstract interface for Dafny drivers."""

    def run(self, inputs: ProverInputs) -> List[ProverOutput]:
        """Run `inputs` and return the prover's output."""
        raise NotImplementedError()


class LSPServer:
    """A simpler wrapper aroudn the Dafny LSP server."""

    ARGS = ["--documents:verify=onchange",
            "--verifier:timelimit=0",
            "--verifier:vcscores=0",
            "--ghost:markStatements=true"]  # FIXME

    def __init__(self, command: List[str]):
        self.command = command
        self.repl = None
        self.pending_output = {}  # Random access queue

    @staticmethod
    def _dump(cmd):
        js = json.dumps(cmd, indent=1)
        # \r\n for consistency, final newline for readability
        return js.replace("\n", "\r\n") + "\r\n"

    def send(self, cmd):
        """Send a request to the server."""
        js = self._dump(cmd)
        header = f"Content-Length: {len(js)}\r\n\r\n"
        debug(">>", repr(header), end="")
        debug(">>", js)
        self.repl.stdin.write(header.encode("utf-8"))
        self.repl.stdin.write(js.encode("utf-8"))
        self.repl.stdin.flush()

    HEADER_RE = re.compile(r"Content-Length: (?P<len>[0-9]+)\r\n")

    def _receive(self):
        line, length = None, None
        while line not in ("", "\r\n"):
            line = self.repl.stdout.readline().decode("utf-8")
            debug("<<", repr(line))
            header = self.HEADER_RE.match(line)
            if header:
                length = int(header.group("len"))
        if length is None:
            raise ValueError(f"Unexpected output: {line!r}")
        response = self.repl.stdout.read(length)
        if len(response) != length:
            raise ValueError(f"Truncated response: {response!r}")
        debug("<<", response)
        js = json.loads(response.decode("utf-8"))
        self.pending_output[response] = js
        return (response, js)

    def receive(self, pred):
        """Read server messages until finding one that matches `pred`."""
        msgs = iter(self.pending_output.items())
        while True:
            key, msg = next(msgs, None) or self._receive()
            if pred(msg):
                del self.pending_output[key]
                return msg

    def _kill(self):
        self.repl.kill()
        try:
            pass  # FIXME
            # self.repl.stdin.close()
            # self.repl.stdout.close()
        finally:
            self.repl.wait()

    def kill(self):
        """Terminate this Dafny instance."""
        repl = self.repl
        if self.repl:
            self._kill()
            self.repl = None
            self.pending_output = []
        return repl

    def _start(self):
        self.kill()

        cmd =  [*self.command, *self.ARGS]
        debug("#", shlex.join(cmd))

        # pylint: disable=consider-using-with
        self.repl = subprocess.Popen(
            cmd, startupinfo=_no_window(),
            stdin=PIPE, stderr=PIPE, stdout=PIPE)

        if TEE:
            log = open(TEE, mode="wb")
            self.repl.stdin = Tee(self.repl.stdin, log)

    def __enter__(self):
        """Start a Dafny LSP server."""
        self._start()
        return self

    def __exit__(self, *_exn):
        """Kill the current Dafny LSP server."""
        self.kill()


class LSPOutput(ProverOutput):
    LEVELS = {1: "Error", }

    def __init__(self, diagnostics: Dict[str, Any]):
        self.diags = diagnostics

    @classmethod
    def _format_diag(cls, d):
        msg = d["message"]
        kind = cls.LEVELS[d["severity"]]
        pos = d['range']['start']
        l, c = pos['line'] + 1, pos['character']
        return f"<stdin>({l},{c}): {kind}: {msg}"

    def format(self):
        """Format to a string matching Dafny's CLI output."""
        return "\n".join(self._format_diag(d) for d in self.diags)


class LSPDriver:
    """A driver using Dafny's LSP implementation."""

    def __init__(self, command: List[str]):
        self.command = which(command)

    @staticmethod
    def is_diagnostic_for(doc):
        """Return a function that checks for diagnostics for `doc`."""
        def _filter(m):
            if m["method"] == LSPMethods.publishDiagnostics:
                mp = m["params"]
                return (mp["version"] == doc["version"] and
                        mp["uri"] == doc["uri"])
            return False
        return _filter

    @staticmethod
    def is_response_to(id: int):
        """Return a function that checks for responses to `id`."""
        return lambda m: m.get("id") == id

    def _iter_results(self, messages: Iterable[LSPOutput]) \
            -> Iterable[LSPMessage]:
        """Feed `inputs` to Dafny's LSP server; return diagnostic messages."""
        with LSPServer(self.command) as server:
            for msg in messages:
                server.send(msg)
                if msg["method"] in LSPMethods.NEED_DIAGNOSTICS:
                    doc = msg["params"]["textDocument"]
                    diag = server.receive(self.is_diagnostic_for(doc))
                    yield LSPOutput(diag["params"]["diagnostics"])
                if "id" in msg:  # Wait for response
                    server.receive(self.is_response_to(msg["id"]))

    def run(self, inputs: ProverInputs) -> List[ProverOutput]:
        """Feed `inputs` to Dafny's LSP server; return diagnostics."""
        messages = inputs.as_lsp().messages
        return list(self._iter_results(messages))


class CLIOutput(ProverOutput):
    ERROR_PATTERN = re.compile(r"^.*?[(][0-9]+,[0-9]+[)].*")

    def __init__(self, output: str):
        self.output = output

    def format(self):
        """Normalize the output of a single Dafny run for easier comparison."""
        messages = self.ERROR_PATTERN.finditer(self.output)
        return "\n".join(m.group() for m in messages)


class CLIDriver:
    """A driver using Dafny's CLI."""

    ARGS = ["/compile:0", "/stdin"]

    def __init__(self, command: List[str]):
        self.command = which(command)

    def _exec(self, snapshot: Snapshot):
        cmd = [*self.command, *self.ARGS]
        return subprocess.run(
            cmd, check=False,
            input=snapshot, encoding="utf-8",
            startupinfo=_no_window(),
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)

    def _iter_results(self, snapshots: Snapshots) \
            -> Iterable[str]:
        for snapshot in snapshots.snapshots:
            yield CLIOutput(self._exec(snapshot).stdout)

    def run(self, inputs: ProverInputs) -> List[ProverOutput]:
        """Run `inputs` through Dafny's CLI and return the prover's output."""
        return list(self._iter_results(inputs.as_snapshots()))


def window(stream: Iterable[T], n: int) -> Iterable[Tuple[T, ...]]:
    """Iterate over `n`-element windows of `stream`."""
    win = deque(maxlen=n)
    for token in stream:
        win.append(token)
        if len(win) == n:
            yield tuple(win)


def test(inputs: ProverInputs, *drivers: Driver):
    """Run `inputs` through each one of `drivers` and report any mismatches."""
    prover_outputs = [d.run(inputs) for d in drivers]
    n_snapshots = len(inputs.as_snapshots())
    assert all(len(po) == n_snapshots for po in prover_outputs)
    for snapidx in range(n_snapshots):
        print(f"=== Snapshot {snapidx} ===")
        for p1, p2 in window(prover_outputs, 2):
            o1, o2 = p1[snapidx].format(), p2[snapidx].format()
            if o1 != o2:
                print(f"Error: {o1} != {o2}")


from pprint import pprint


def _test_snapshots():
    d = CLIDriver(["Dafny"])
    inputs = Snapshots.from_files("snaps.dfy")
    for m in d.run(inputs):
        print(m.format())


def _test_snapshots_lsp():
    lsp = Snapshots.from_files("snaps.dfy").as_lsp()
    dll = r"C:\Users\cpitcla\git\dafny\Binaries\DafnyLanguageServer.dll"
    driver = LSPDriver(["dotnet", dll])
    pprint(driver.run(lsp))


def _test_diff():
    inputs = Snapshots.from_files("snaps.dfy")
    dll = r"C:\Users\cpitcla\git\dafny\Binaries\DafnyLanguageServer.dll"
    test(inputs, LSPDriver(["dotnet", dll]), CLIDriver(["Dafny"]))

if __name__ == "__main__":
    _test_diff()
    # _test_snapshots()
    # _test_snapshots_lsp()
