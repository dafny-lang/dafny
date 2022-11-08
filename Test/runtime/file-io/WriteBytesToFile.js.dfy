// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target:js "%s" -- "%t.data" >> "%t"
// RUN: %diff "%S/WriteBytesToFile.expect" "%t"
// RUN: %diff "%S/WriteBytesToFile.data.expect" "%t.data"

include "./AbstractWriteBytesToFile.dfy"
include "./FileIO.js.dfy"

module Test refines AbstractTest {
  import AbstractFileIO = FileIO

  function method ExpectedErrorMessagePrefix(): string {
    "Error: ENOENT"
  }
}
