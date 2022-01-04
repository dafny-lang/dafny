#!/usr/bin/env python3
"""A differential tester for Dafny.

This program takes a list of Dafny frontends and a list of inputs and runs each
input through each frontend.  Verification results are then compared to ensure
that they match.

A frontend is an executable (either the Dafny CLI ``Dafny.exe`` or the Dafny LSP
Server ``DafnyLanguageServer.exe``) plus the arguments to pass to it.

An input is either a Dafny file (``.dfy``) or an LSP trace (``.lsp``).  If given
a file ``xyz.dfy``, this program first looks for a sequence of snapshots
``xyz.v0.dfy``, ``xyz.v1.dfy``, etc. before falling back to ``xyz.dfy``.

Limitations:

- This only checks error messages, not return codes

- This only checks for errors in the "main" file, not in all files reported by
  the LSP server.

Example usage::

   ./difftester.py --frontend Dafny \
                   --frontend DafnyLanguageServer \
                   --input snaps.dfy

"""

from typing import (
    Any, Callable, Dict, Iterable, Iterator, IO, List, NamedTuple,
    Optional, Tuple, TypeVar, Union, overload
)

import argparse
import difflib
import json
import os
import platform
import re
import shlex
import shutil
import subprocess
import sys
import urllib.parse

from collections import deque
from concurrent.futures import ThreadPoolExecutor
from itertools import zip_longest
from pathlib import Path
from subprocess import PIPE
from pprint import pformat
from textwrap import indent

# For ordered dicts and f-strings
assert sys.version_info >= (3, 7)

T = TypeVar("T")
Json = Dict[str, Any]

LSPMessage = Json
"""A single LSP client request."""

VERBOSITY = 0
INPUT_TEE = "inputs.log"
OUTPUT_TEE = "outputs.log"

NWORKERS = 1
TIMEOUT = 6000.0  # https://stackoverflow.com/questions/1408356/

RELATED_LOCATION = "Related location"
"""String used by Dafny to indicate a relatedInformation message."""

@overload
def which(exe: str) -> str: ...
@overload
def which(exe: List[str]) -> List[str]: ...

def which(exe: Union[str, List[str]]) -> Union[str, List[str]]:
    """Locate executable `exe`; raise a ``ValueError`` if it can't be found."""
    if isinstance(exe, list):
        return [which(exe[0]), *exe[1:]]
    path = shutil.which(exe)
    if path is None:
        raise ValueError(f"Executable not found in PATH: {exe}")
    return path


def _print(level: int, prefix: str, *msgs: str, **kwargs: Any) -> None:
    """Print `msgs` with `prefix` if `level` <= ``VERBOSITY``.

    Keywords `kwargs` are forwarded to ``print``.
    """
    if level <= VERBOSITY:
        print(prefix, *msgs, **{**kwargs, "file": sys.stderr})  # type: ignore


def info(prefix: str, *msgs: str, **kwargs: Any) -> None:
    """Call ``_print`` with `prefix`, `msgs`, and `kwargs` at level 1."""
    _print(1, prefix, *msgs, **kwargs)


def debug(prefix: str, *msgs: str, **kwargs: Any) -> None:
    """Call ``_print`` with `prefix`, `msgs`, and `kwargs` at level 2."""
    _print(2, prefix, *msgs, **kwargs)


def trace(prefix: str, *msgs: str, **kwargs: Any) -> None:
    """Call ``_print`` with `prefix`, `msgs`, and `kwargs` at level 2."""
    _print(3, prefix, *msgs, **kwargs)


def _no_window() -> subprocess.STARTUPINFO:
    """Create a startupinfo object.

    On Windows, set it up to run without showing a command window.
    """
    si = subprocess.STARTUPINFO()
    if platform.system() == "Windows":
        # No new window
        si.dwFlags |= subprocess.STARTF_USESHOWWINDOW
        # “Terminate batch job?” on Ctrl+C, but that blocks the parent process
        # si.dwFlags |= subprocess.CREATE_NEW_PROCESS_GROUP
    return si


class InputTee(IO[bytes]):
    """Wrapper around a collection of streams that broadcasts writes."""

    def __init__(self, *streams: IO[bytes]) -> None:
        self.streams = streams

    def close(self) -> None:
        for s in self.streams:
            s.close()

    def write(self, data: bytes) -> int:
        return max(s.write(data) for s in self.streams)

    def flush(self) -> None:
        for s in self.streams:
            s.flush()


class RecorderTee(IO[bytes]):
    """Wrapper around a stream that records reads from it."""

    def __init__(self, stream: IO[bytes], log: IO[bytes]) -> None:
        self.stream, self.log = stream, log

    def read(self, n: int) -> bytes:
        bs = self.stream.read(n)
        self.log.write(bs)
        return bs

    def readline(self) -> bytes:
        bs = self.stream.readline()
        self.log.write(bs)
        return bs

    def close(self) -> None:
        for s in (self.stream, self.log):
            s.close()

    def flush(self) -> None:
        self.log.flush()


class Snapshot:
    """The contents of a Dafny file."""

    def __init__(self, name: str, contents: str) -> None:
        self.name = name
        self.contents = contents

    @staticmethod
    def from_file(path: Union[str, Path]) -> "Snapshot":
        pth = Path(path)
        return Snapshot(pth.name, pth.read_text(encoding="utf-8"))

    def __str__(self) -> str:
        return self.contents


class ProverInputs:
    """A sequence of inputs to Dafny."""

    name: str

    def as_lsp(self) -> "LSPTrace":
        """Convert self into an LSP trace."""
        raise NotImplementedError

    def as_snapshots(self) -> "Snapshots":
        """Convert self into a sequence of snapshots."""
        raise NotImplementedError

    def __len__(self) -> int:
        raise NotImplementedError


class VerificationResult(NamedTuple):
    """Structured output returned by Dafny."""
    fname: str
    line: int
    col: int
    header: str
    msg: str
    children: "List[VerificationResult]"

    def format(self) -> List[str]:
        sep = ": " if self.header and self.msg else ""
        line = f"{self.fname}({self.line},{self.col}): {self.header}{sep}{self.msg}"
        return [line, *(ll for vr in self.children for ll in vr.format())]


class ProverOutput:
    """An output of Dafny."""

    def normalize(self) -> Iterable[VerificationResult]:
        """Normalize this output and convert it to a list of results."""
        raise NotImplementedError

    # Strings are easier to diff than structured data, especially when looking
    # at insertions/deletions.
    def format(self) -> str:
        """Normalize this output and convert it to a string."""
        return "\n".join(ll.replace("\r\n", "\n") # Ignore line ending differences
                         for vr in sorted(self.normalize())
                         for ll in vr.format())

    @property
    def raw(self) -> Any:
        """Return the raw output of the prover."""
        raise NotImplementedError


class LSPMethods:
    """Global constants for LSP Methods."""
    didOpen = "textDocument/didOpen"
    didChange = "textDocument/didChange"
    publishDiagnostics = "textDocument/publishDiagnostics"
    compilationStatus = "dafny/compilation/status"
    NEED_DIAGNOSTICS = {didOpen, didChange}


class LSPReader:
    HEADER_RE = re.compile(r"Content-Length: (?P<len>[0-9]+)\r\n")

    def __init__(self, stream: IO[bytes]) -> None:
        self.stream = stream

    def read_one(self, verbose=False) -> Tuple[bytes, Json]:
        line, length = None, None
        while line not in ("", "\r\n"):
            line = self.stream.readline().decode("utf-8")
            if verbose:
                trace("<<", repr(line))
            header = self.HEADER_RE.match(line)
            if header:
                length = int(header.group("len"))
        if line == "":
            raise EOFError
        if length is None:
            MSG = (f"Unexpected output: {line!r}, use -vvv for a trace."
                   "If -vvv doesn't help, check Dafny's server logs "
                   "(https://github.com/dafny-lang/ide-vscode#debugging).")
            raise ValueError(MSG)
        response: bytes = self.stream.read(length)
        if len(response) != length:
            raise ValueError(f"Truncated response: {response!r}")
        resp = response.decode("utf-8")
        if verbose:
            trace("<<", resp)
        return response, json.loads(resp)

    def read(self, verbose=True):
        try:
            while True:
                yield self.read_one(verbose=verbose)
        except EOFError:
            pass


class LSPDocument:
    def __init__(self):
        self.document = "" # Calculations below assume utf-16 representation

    def find_nth_bol(self, n: int) -> int:
        bol = 0
        for _ in range(n):
            bol = self.document.find("\n", bol)
            if bol < 0:
                raise ValueError(f"Invalid line number: {n}")
            bol += 1
        return bol

    def loc2offset(self, loc: Json):
        line, char = int(loc["line"]), int(loc["character"])
        assert line >= 0, char >= 0
        return self.find_nth_bol(line) + char

    def update(self, change: Json) -> str:
        rng, text = change.get("range"), change["text"]
        if rng is None:
            self.document = text
        else:
            beg = self.loc2offset(rng["start"])
            end = self.loc2offset(rng["end"])
            self.document = self.document[:beg] + text + self.document[end:]
        return self.document


class LSPTrace(ProverInputs):
    """A sequence of messages sent by an LSP client."""

    def __init__(self, name: str, commands: Iterable[LSPMessage]) -> None:
        self.name = name
        self.messages: List[LSPMessage] = list(commands)

    @classmethod
    def from_json_file(cls, fname: str) -> "LSPTrace":
        """Load an LSP trace from a JSON file."""
        with open(fname, encoding="utf-8") as f:
            return LSPTrace(fname, json.load(f))

    @classmethod
    def from_dump_file(cls, fname: str) -> "LSPTrace":
        """Load an LSP trace from a file containing JSON."""
        with open(fname, mode="rb") as f:
            return LSPTrace(fname, (js for _, js in LSPReader(f).read()))

    def as_lsp(self) -> "LSPTrace":
        """Convert self into an LSP trace."""
        return self

    def _iter_snapshots(self) -> Iterable[str]:
        doc = LSPDocument()
        for msg in self.messages:
            if msg.get("method") == LSPMethods.didOpen:
                yield doc.update(msg["params"]["textDocument"])
            if msg.get("method") == LSPMethods.didChange:
                for change in msg["params"]["contentChanges"]:
                    yield doc.update(change)

    @property
    def uri(self) -> str:
        """Return the current document's URI."""
        for m in self.messages:
            if m.get("method") == LSPMethods.didOpen:
                return m["params"]["textDocument"]["uri"]  # type: ignore
        raise ValueError("No didOpen message found in LSP trace.")

    def _snapshot_name(self, idx: int) -> str:
        return str(Path(self.name).with_suffix(f".v{idx}.dfy"))

    def as_snapshots(self) -> "Snapshots":
        """Convert self into a sequence of snapshots."""
        snapshots = (Snapshot(self._snapshot_name(idx), s)
                     for idx, s in enumerate(self._iter_snapshots()))
        return Snapshots(self.name, self.uri, snapshots)

    def __len__(self) -> int:
        return sum(msg.get("method") in (LSPMethods.didOpen, LSPMethods.didChange)
                   for msg in self.messages)


class Snapshots(ProverInputs):
    """A sequence of Dafny files."""

    VERNUM_RE = re.compile(r"\A(?P<stem>.*)[.]v(?P<num>[0-9]+)\Z")

    def __init__(self, name: str, uri: str, snapshots: Iterable[Snapshot]) -> None:
        self.name = name
        self.uri = uri
        self.snapshots = list(snapshots)

    @classmethod
    def strip_vernum(cls, fname: Union[str, Path]) -> Tuple[str, Optional[int], str]:
        """Split `fname` into a stem, a suffix, and a version number.

        >>> Snapshots.strip_vernum("a.v0.dfy")
        ('a', 0, '.dfy')
        >>> Snapshots.strip_vernum("a.dfy")
        ('a', None, '.dfy')
        """
        pth = Path(fname)
        mnum = cls.VERNUM_RE.match(pth.stem)
        if not mnum:
            return pth.stem, None, pth.suffix
        return mnum.group("stem"), int(mnum.group("num")), pth.suffix


    @classmethod
    def _find_snapshot_files(cls, name: str) -> Iterable[Tuple[int, Path]]:
        """Yield paths matching stem.vN.suffix where stem.suffix is `name`."""
        ref = Path(name)
        if ref.exists():
            yield 0, ref
            return
        for f in ref.parent.iterdir():
            stem, num, suffix = cls.strip_vernum(f)
            if ref.stem == stem and ref.suffix == suffix and num is not None:
                yield num, f

    @classmethod
    def from_files(cls, name: str) -> "Snapshots":
        """Read file `name` from file.

        If `name` does not exist, read all files matching stem.vN.suffix, where
        stem.suffix is `name`.
        """
        files = [f for _, f in sorted(cls._find_snapshot_files(name))]
        snaps = (Snapshot.from_file(f) for f in files)
        uri = Path(name).absolute().as_uri()
        return Snapshots(name, uri, snaps)

    @classmethod
    def _complete_range(cls, previous: Snapshot) -> Json:
        contents = str(previous)
        last_line = contents.count("\n")
        last_bol = contents.rfind("\n") + 1
        last_pos = len(contents[last_bol:].encode("utf-16le"))
        return {"start": {"line": 0, "character": 0},
                "end": {"line": last_line, "character": last_pos}}

    @classmethod
    def _lsp_of_snapshot(cls, uri: str, version: int, snapshot: Snapshot,
                         previous: Optional[Snapshot]) -> LSPMessage:
        document = {"uri": uri, "languageId": "dafny", "version": version}
        return {
            "method": LSPMethods.didOpen,
            "params": {"textDocument": {**document, "text": str(snapshot)}}
        } if previous is None else {
            "method": LSPMethods.didChange,
            "params": {"textDocument": document,
                       "contentChanges": [{
                           "text": str(snapshot),
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
            idd = {"id": id} if msg.get("method") in METHODS else {}
            yield {"jsonrpc": "2.0", **msg, **idd}

    def as_lsp(self) -> "LSPTrace":
        """Convert self into an LSP trace."""
        return LSPTrace(self.name, self._iter_jrpc())

    def as_snapshots(self) -> "Snapshots":
        """Convert self into a sequence of snapshots."""
        return self

    def __iter__(self) -> Iterator[Snapshot]:
        return iter(self.snapshots)

    def __len__(self) -> int:
        return len(self.snapshots)

class Frontend:
    """Abstract interface for Dafny frontends."""

    def __init__(self, command: List[str]) -> None:
        self.command = which(command)

    def run(self, inputs: ProverInputs) -> Iterable[ProverOutput]:
        """Run `inputs` and return the prover's outputs."""
        raise NotImplementedError()

    def __repr__(self) -> str:
        return f"{type(self).__name__}(command={self.command})"


class LSPServer:
    """A simpler wrapper aroudn the Dafny LSP server."""

    ARGS = ["--documents:verify=onchange"]  # FIXME

    def __init__(self, command: List[str]) -> None:
        self.command = command
        self.listeners: List[Callable[[Json], None]] = []
        self.repl: "Optional[subprocess.Popen[bytes]]" = None
        self.pending_output: Dict[bytes, LSPMessage] = {}  # Random access queue

    @staticmethod
    def _dump(cmd: LSPMessage) -> str:
        js = json.dumps(cmd, indent=1)
        # \r\n for consistency, final newline for readability
        return js.replace("\n", "\r\n") + "\r\n"

    @staticmethod
    def _adjust_cmd(cmd: LSPMessage) -> LSPMessage:
        """Make small changes to `cmd` to ensure that it can run.

        For now the only change needed is updating the ``processId`` in
        ``initialize`` messages.

        https://microsoft.github.io/language-server-protocol/specification#initialize
        """
        if cmd["method"] == "initialize":
            cmd = {**cmd,  # Avoid mutating the original ``cmd``.
                   "params": {**cmd["params"],
                              "processId": os.getpid()}}
        return cmd

    def send(self, cmd: LSPMessage) -> None:
        """Send a request to the server."""
        assert self.repl
        assert self.repl.stdin
        js = self._dump(self._adjust_cmd(cmd))
        header = f"Content-Length: {len(js)}\r\n\r\n"
        trace(">>", repr(header))
        trace(">>", js)
        self.repl.stdin.write(header.encode("utf-8"))
        self.repl.stdin.write(js.encode("utf-8"))
        self.repl.stdin.flush()

    def listen(self, listener: Callable[[Json], None]):
        """Register a `listener` to which all LSP messages should be sent."""
        self.listeners.append(listener)

    def _call_listeners(self, js: Json) -> None:
        for callback in self.listeners:
            callback(js)

    def _receive(self) -> Tuple[bytes, Json]:
        assert self.repl
        assert self.repl.stdout
        response, js = LSPReader(self.repl.stdout).read_one(verbose=True)
        self.pending_output[response] = js
        self._call_listeners(js)
        return (response, js)

    def receive(self, pred: Callable[[LSPMessage], bool]) -> LSPMessage:
        """Read server messages until finding one that matches `pred`."""
        msgs = iter(list(self.pending_output.items()))
        while True:
            key, msg = next(msgs, None) or self._receive()  # type: ignore
            if pred(msg):
                del self.pending_output[key]
                return msg

    def discard_pending_messages(self):
        """Discard pending server messages."""
        self.pending_output.clear()

    def _kill(self) -> None:
        assert self.repl and self.repl.stdin and self.repl.stdout
        self.repl.kill()
        try:
            self.repl.stdin.close()
            self.repl.stdout.close()
        finally:
            self.repl.wait()

    def kill(self) -> "Optional[subprocess.Popen[bytes]]":
        """Terminate this Dafny instance."""
        repl = self.repl
        if self.repl:
            self._kill()
            self.repl = None
            self.pending_output = {}
        return repl

    def _start(self) -> None:
        self.kill()

        cmd = [*self.command, *self.ARGS]
        debug("#", shlex.join(cmd))

        # pylint: disable=consider-using-with
        self.repl = subprocess.Popen(
            cmd, startupinfo=_no_window(),
            stdin=PIPE, stderr=PIPE, stdout=PIPE)

        if INPUT_TEE:
            assert self.repl.stdin
            log = open(INPUT_TEE, mode="wb")
            self.repl.stdin = InputTee(self.repl.stdin, log)  # type: ignore

        if OUTPUT_TEE:
            assert self.repl.stdout
            log = open(OUTPUT_TEE, mode="wb")
            self.repl.stdout = RecorderTee(self.repl.stdout, log)  # type: ignore

    def __enter__(self) -> "LSPServer":
        """Start a Dafny LSP server."""
        self._start()
        return self

    def __exit__(self, *_exn: Any) -> None:
        """Kill the current Dafny LSP server."""
        self.kill()


class LSPOutput(ProverOutput):
    LEVELS = {1: "Error", 2: "Warning", 4: "Info"}

    def __init__(self, diagnostics: List[Json]) -> None:
        lines = [d["range"]["start"]["line"] for d in diagnostics]
        debug("[lsp]", f"{len(diagnostics)} diagnostics (lines: {lines})")
        self.diags = diagnostics

    @classmethod
    def _normalize_one(cls, pos: Json, header: str, msg: str,
                       children: List[VerificationResult]) -> VerificationResult:
        """Convert an LSP diagnostic `pos`, `msg`, `header`, `children` into a ``VerificationResult``."""
        l, c = pos['line'] + 1, pos['character']
        msg = msg.replace("\n", "\n ") # The CLI does this to make messages easier to match
        return VerificationResult("<stdin>", l, c, header, msg, children)

    @classmethod
    def _normalize_related(cls, ri: LSPMessage) -> VerificationResult:
        # FIXME: Check URI
        pos, msg = ri["location"]["range"]["start"], ri["message"]
        header = RELATED_LOCATION if msg != RELATED_LOCATION else ""
        return cls._normalize_one(pos, header, msg, [])

    @classmethod
    def _normalize_diag(cls, d: LSPMessage) -> Iterator[VerificationResult]:
        kind = cls.LEVELS[d["severity"]]
        pos, msg = d["range"]["start"], d["message"]
        related = d.get("relatedInformation", [])
        if "File contains no code" in msg:
            assert not related # Skip these errors
            return
        children = [cls._normalize_related(ri) for ri in related]
        yield cls._normalize_one(pos, kind, msg, children=children)

    def normalize(self) -> Iterable[VerificationResult]:
        """Normalize this output and convert it to a list of results."""
        for d in self.diags:
            yield from self._normalize_diag(d)

    @property
    def raw(self) -> List[Json]:
        """Return the raw output of the prover."""
        return self.diags


def same_uri(u1, u2):
    """Try to check whether `u1` and `u2` refer to the same resource.

    This is needed because Dafny's LSP server unquotes URIs."""
    return urllib.parse.unquote(u1) == urllib.parse.unquote(u2)


class LSPFrontend(Frontend):
    """A frontend using Dafny's LSP implementation."""

    @staticmethod
    def is_diagnostic_for(doc: Json) -> Callable[[LSPMessage], bool]:
        """Return a function that checks for diagnostics for `doc`."""
        def _filter(m: LSPMessage) -> bool:
            if m.get("method") == LSPMethods.publishDiagnostics:
                mp = m["params"]
                return (mp["version"] == doc["version"] and  # type: ignore
                        same_uri(mp["uri"], doc["uri"]))
            return False
        return _filter

    @staticmethod
    def is_response_to(id: int) -> Callable[[LSPMessage], bool]:
        """Return a function that checks for responses to `id`."""
        return lambda m: m.get("id") == id

    @staticmethod
    def is_verified_notification() -> Callable[[LSPMessage], bool]:
        """Return a function that checks for a message indicating completion."""
        def _filter(m: LSPMessage) -> bool:
            if m.get("method") == LSPMethods.compilationStatus:
                st = m["params"]["status"]
                return "Succeeded" in st or "Failed" in st
            return False
        return _filter

    @staticmethod
    def _log_progress(m: Json):
        """Log LSP message `m` if it signals verification progress."""
        if m.get("method") == LSPMethods.compilationStatus:
            trace("[lsp]", f"Verifying: {m['params'].get('message', '...')}")

    def _receive_diagnostics(self, doc: Json, server: LSPServer):
        """Wait for a verified status message and a set of diagnostics."""
        # Drop stale output
        server.discard_pending_messages()
        # Wait for verification to complete
        _ = server.receive(self.is_verified_notification())
        # Ignore partial diagnostics
        server.discard_pending_messages()
        # Read final diagnostic message
        diag = server.receive(self.is_diagnostic_for(doc))
        return LSPOutput(diag["params"]["diagnostics"])

    def _iter_results(self, messages: Iterable[LSPMessage]) \
            -> Iterable[LSPOutput]:
        """Feed `inputs` to Dafny's LSP server; return diagnostic messages."""
        with LSPServer(self.command) as server:
            server.listen(self._log_progress)
            for msg in messages:
                server.send(msg)
                if msg.get("method") in LSPMethods.NEED_DIAGNOSTICS:
                    doc = msg["params"]["textDocument"]
                    yield self._receive_diagnostics(doc, server)
                if "id" in msg:  # Wait for response
                    server.receive(self.is_response_to(msg["id"]))

    def run(self, inputs: ProverInputs) -> Iterable[ProverOutput]:
        """Run `inputs` through Dafny's LSP server; return diagnostics."""
        messages = inputs.as_lsp().messages
        yield from self._iter_results(messages)


class CLIOutput(ProverOutput):
    ERROR_PATTERN = re.compile(r"""
      ^
       (?P<fname><stdin>)
       [(](?P<l>[0-9]+),
          (?P<c>[0-9]+)[)]
       ((?P<hdr>[^:]*):[ ]*)?
       (?P<msg>.*(\n[ ].+)*)
      $
    """, re.MULTILINE | re.VERBOSE)

    def __init__(self, output: str) -> None:
        self.output = output

    def _normalize(self) -> Iterable[VerificationResult]:
        last = None
        for m in self.ERROR_PATTERN.finditer(self.output):
            fname, l, c, hdr, msg = m.group("fname", "l", "c", "hdr", "msg")
            vr = VerificationResult(fname, int(l), int(c), hdr or "", msg or "", [])
            if (RELATED_LOCATION in vr.header or RELATED_LOCATION in vr.msg):
                assert last
                last.children.append(vr)
            else:
                last = vr
                yield last

    def normalize(self) -> Iterable[VerificationResult]:
        """Normalize this output and convert it to a list of results."""
        return list(self._normalize()) # Force list to collect all children

    @property
    def raw(self) -> str:
        """Return the raw output of the prover."""
        return self.output

class CLIFrontend(Frontend):
    """A frontend using Dafny's CLI."""

    ARGS = ["/compile:0", "/stdin"]

    def _exec(self, snapshot: Snapshot) -> "subprocess.CompletedProcess[str]":
        cmd = [*self.command, *self.ARGS]
        debug("#", shlex.join(cmd), "<", snapshot.name)
        return subprocess.run(
            cmd, check=False,
            input=str(snapshot), encoding="utf-8",
            startupinfo=_no_window(),
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)

    def _collect_one_output(self, snapshot: Snapshot) -> CLIOutput:
        return CLIOutput(self._exec(snapshot).stdout)

    def _iter_results(self, snapshots: Snapshots) -> Iterable[CLIOutput]:
        with ThreadPoolExecutor(max_workers=NWORKERS) as exc:
            yield from exc.map(self._collect_one_output,
                               snapshots, timeout=TIMEOUT)

    def run(self, inputs: ProverInputs) -> Iterable[ProverOutput]:
        """Run `inputs` through Dafny's CLI; return the prover's outputs."""
        yield from self._iter_results(inputs.as_snapshots())


def window(stream: Iterable[T], n: int) -> Iterable[Tuple[T, ...]]:
    """Iterate over `n`-element windows of `stream`."""
    win: "deque[T]" = deque(maxlen=n)
    for token in stream:
        win.append(token)
        if len(win) == n:
            yield tuple(win)


def test(inputs: ProverInputs, *frontends: Frontend) -> None:
    """Run `inputs` through each one of `frontends` and report any mismatches."""
    retval = 0
    snapshots = inputs.as_snapshots()
    prover_output_streams = [d.run(inputs) for d in frontends]
    # zip() would be unsafe here (it wouldn't exhaust the iterator over the LSP
    # server's results and hence wouldn't send the “shutdown” message).
    results = zip_longest(*prover_output_streams)
    for snapidx, snap in enumerate(snapshots):
        info(f"------ {snap.name}(#{snapidx}) ------", flush=True)
        prover_outputs: List[ProverOutput] = next(results)
        for (d1, p1), (d2, p2) in window(zip(frontends, prover_outputs), 2):
            o1, o2 = p1.format(), p2.format()
            if o1 != o2:
                print("!! Output mismatch")
                print(f"   For input {snap.name}(#{snapidx}),")

                print()
                print(f"   Frontend {d1} produced this output:")
                print(indent(o1, "     "))

                print()
                print(f"   Frontend {d2} produced this output:")
                print(indent(o2, "     "))

                print()
                l1, l2 = o1.splitlines(keepends=True), o2.splitlines(keepends=True)
                ld = difflib.unified_diff(l1, l2, str(d1), str(d2))
                print(f"   Diff:")
                print(indent("".join(ld), "     "))
                sys.stdout.flush()

                debug("")
                debug("   Raw output:")
                debug(indent(pformat(p1.raw), "     "))
                debug("   --------------------------------")
                debug(indent(pformat(p2.raw), "     "))
                sys.stderr.flush()
                retval += 1
        sys.stdout.flush()
    for _ in results:
        # Exhaust results iterators to make sure LSPServer calls shutdown and
        # exit (without this LSP commands after the last didChange are never sent).
        pass
    return retval


SLASH_2DASHES = re.compile("^/(?=--)")


def resolve_frontend(command: List[str]) -> Frontend:
    """Resolve `command` into a ``Frontend`` instance."""
    command = [SLASH_2DASHES.sub("", c) for c in command]
    if "DafnyLanguageServer" in command[0]:
        return LSPFrontend(command)
    return CLIFrontend(command)


def resolve_input(inp: str, parser: argparse.ArgumentParser) -> ProverInputs:
    """Resolve file name `inp` into a ``ProverInputs`` instance.

    Report errors through `parser`."""
    stem, num, suffix = Snapshots.strip_vernum(inp)

    if num is not None:
        MSG = (f"WARNING: File name {inp} looks like a single snapshot.  "
               "To verify multiple snapshots, call this program on "
               f"{stem}{suffix}.")
        print(MSG, file=sys.stderr, flush=True)

    if suffix == ".dfy":
        return Snapshots.from_files(inp)
    if suffix == ".lsp":
        return LSPTrace.from_dump_file(inp)
    MSG = (f"{inp}: Unsupported file extension {suffix!r} "
           "(only .dfy and .lsp inputs are supported for now).")
    parser.error(MSG)
    assert False # Unreachable


def parse_arguments() -> argparse.Namespace:
    """Parser command line arguments."""
    parser = argparse.ArgumentParser(description=__doc__)

    parser.add_argument('--verbose', '-v', action='count', default=0,
                        help="Increase verbosity (repeat for more).")

    J_HELP = "Run command line tests in N concurrent threads."
    parser.add_argument("-j", type=int, default=None,
                        metavar="N", help=J_HELP)

    TIMEOUT_HELP = "Limit execution time to N seconds for individual CLI runs."
    parser.add_argument("--timeout", type=int, default=None,
                        metavar="N", help=TIMEOUT_HELP)

    parser.add_argument("--frontend", required=True,
                        nargs="+", action="append", dest="frontends",
                        metavar=("FRONTEND_NAME", "ARGUMENTS"),
                        help="Register a frontend")

    parser.add_argument("--input", required=True,
                        metavar="INPUT", action="append", dest="inputs",
                        help="Register an input file")

    args, argv = parser.parse_known_args()
    if argv:
        MSG = (f"Unrecognized arguments: {' '.join(argv)}.  "
               "If these were meant as arguments to a --frontend, "
               "prefix them with a slash.  For example, use "
               "/--verifier:cachingPolicy=0 instead of "
               "--verifier:cachingPolicy=0.")
        parser.error(MSG)
    args.frontends = [resolve_frontend(d) for d in args.frontends]
    args.inputs = [resolve_input(d, parser) for d in args.inputs]

    global VERBOSITY
    VERBOSITY = args.verbose

    if args.j:
        global NWORKERS
        NWORKERS = args.j

    if args.timeout:
        global TIMEOUT
        TIMEOUT = args.timeout

    return args


def main() -> None:
    retval = 0
    args = parse_arguments()
    for inputs in args.inputs:
        info(f"====== {inputs.name} ======", file=sys.stderr)
        retval += test(inputs, *args.frontends)
    return retval


if __name__ == "__main__":
    try:
        sys.exit(main() != 0)
    except KeyboardInterrupt:
        sys.exit(0)
