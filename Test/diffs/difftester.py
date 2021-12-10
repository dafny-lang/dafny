#!/usr/bin/env python3
"""Differential tester for Dafny."""

from typing import Any, Iterable, List, Tuple

import re
import shutil
import subprocess
from pathlib import Path


LSPTrace = List[Any]
"""A sequence of commands sent by an LSP client."""

Snapshot = bytes
"""The contents of a Dafny file."""

VerificationResult = List[bytes]
"""Structured output returned by Dafny."""


def which(exe):
    """Locate executable `exe`; raise a ``ValueError`` if it can't be found."""
    path = shutil.which(exe)
    if path is None:
        raise ValueError("Executable not found in PATH: {}".format(exe))
    return path


class Snapshots:
    VERNUM_RE = re.compile(r"\A(?P<stem>.*)[.]v(?P<num>[0-9]+)\Z")

    @classmethod
    def _iter_snapshots(cls, name: str) -> Iterable[Tuple[int, Path]]:
        """Yield paths matching stem.vN.suffix when `name` is stem.suffix."""
        ref = Path(name)
        for f in ref.parent.iterdir():
            if ref.suffix == f.suffix:
                mnum = cls.VERNUM_RE.match(f.stem)
                if mnum and ref.stem == mnum.group("stem"):
                    yield int(mnum.group("num")), f

    @classmethod
    def read_snapshots(cls, name: str) -> Iterable[Snapshot]:
        """Read files matching stem.vN.suffix when `name` is stem.suffix."""
        return [f.read_bytes() for _, f in sorted(cls._iter_snapshots(name))]

    @classmethod
    def lsp_trace_of_snapshots(cls, snapshots: List[Snapshot]) -> LSPTrace:
        """Convert a sequence of `snapshots` into a basic LSP trace."""
        return snapshots # FIXME

    @classmethod
    def snapshots_of_lsp_trace(cls, trace: LSPTrace) -> List[Snapshot]:
        """Extract a sequence of snapshots from an LSP `trace`."""
        return trace # FIXME


class Driver():
    """Abstract interface for Dafny drivers."""

    def run(self, trace: LSPTrace) -> List[VerificationResult]:
        """Run a `trace` of LSP commands and return the prover's output."""
        raise NotImplementedError()


class LSPDriver():
    """A driver using Dafny's LSP implementation."""

    def run(self, trace: LSPTrace) -> List[VerificationResult]:
        """Run a `trace` of LSP commands and return the prover's output."""
        raise NotImplementedError()


class CLIDriver():
    """A driver using Dafny's CLI."""

    ARGS = ["/compile:0", "/stdin"]

    def __init__(self, args: List[str], executable="dafny"):
        self.user_args = args
        self.executable = which(executable)

    def _exec(self, snapshot: Snapshot):
        cmd = [self.executable, *self.user_args, *self.ARGS]
        # FIXME avoid creating a window
        si = subprocess.STARTUPINFO()
        si.dwFlags |= subprocess.STARTF_USESHOWWINDOW
        return subprocess.run(cmd, input=snapshot, check=False, startupinfo=si,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT)

    def _iter_results(self, trace: LSPTrace) -> Iterable[VerificationResult]:
        for snapshot in Snapshots.snapshots_of_lsp_trace(trace):
            yield self._exec(snapshot)

    def run(self, trace: LSPTrace) -> List[VerificationResult]:
        """Run a `trace` of LSP commands and return the prover's output."""
        return list(self._iter_results(trace))


def test(trace: LSPTrace, *drivers):
    """Run `trace` through each one of `drivers` and report any mismatches."""
    outputs = [d.run(trace) for d in drivers]
    for i in range(len(outputs) - 1):
        if outputs[i] != outputs[i + 1]:
            print("Error")

def test_snapshots():
    d = CLIDriver([])
    trace = Snapshots.lsp_trace_of_snapshots(Snapshots.read_snapshots("snaps.dfy"))
    print(d.run(trace))

if __name__ == "__main__":
    test_snapshots()
