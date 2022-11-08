// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target:js "%s" -- "%S/ReadBytesFromFile.data" >> "%t"
// RUN: %diff "%S/ReadBytesFromFile.expect" "%t"

include "./AbstractReadBytesFromFile.dfy"
include "./FileIO.js.dfy"

module Test refines AbstractTest {
  import AbstractFileIO = FileIO

  function method ExpectedErrorMessagePrefix(): string {
    "Error: ENOENT"
  }
}
