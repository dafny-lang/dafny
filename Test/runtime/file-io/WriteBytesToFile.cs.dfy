// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target:cs "%s" -- "%t.data" >> "%t"
// RUN: %diff "%S/WriteBytesToFile.expect" "%t"
// RUN: %diff "%S/WriteBytesToFile.data.expect" "%t.data"

include "./AbstractWriteBytesToFile.dfy"
include "./FileIO.cs.dfy"

module Test refines AbstractTest {
  import AbstractFileIO = FileIO

  function method ExpectedErrorMessagePrefix(): string {
    "System.ArgumentException: "
  }
}
