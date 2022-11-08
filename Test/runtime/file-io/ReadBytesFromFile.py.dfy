// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target:py "%s" -- "%S/ReadBytesFromFile.dfy.data" >> "%t"
// RUN: %diff "%S/ReadBytesFromFile.dfy.expect" "%t"

include "./ReadBytesFromFile.dfy"
include "./FileIO.py.dfy"

module Test refines AbstractTest {
  import FileIO = FileIO_Python

  function method ExpectedErrorMessagePrefix(): string {
    "[Errno 2]"
  }
}
