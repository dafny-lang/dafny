// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target:py "%s" -- "%t.data" >> "%t"
// RUN: %diff "%S/WriteBytesToFile.expect" "%t"
// RUN: %diff "%S/WriteBytesToFile.data.expect" "%t.data"

include "./AbstractWriteBytesToFile.dfy"
include "./FileIO.py.dfy"

module Test refines AbstractTest {
  import FileIO = FileIO_Python

  function method ExpectedErrorMessagePrefix(): string {
    "[Errno 2]"
  }
}
