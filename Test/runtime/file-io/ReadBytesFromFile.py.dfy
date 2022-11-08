// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target:py "%s" -- "%S/ReadBytesFromFile.data" >> "%t"
// RUN: %diff "%S/ReadBytesFromFile.expect" "%t"

include "./AbstractReadBytesFromFile.dfy"
include "./FileIO.py.dfy"

module Test refines AbstractTest {
  import AbstractFileIO = FileIO

  function method ExpectedErrorMessagePrefix(): string {
    "[Errno 2]"
  }
}
