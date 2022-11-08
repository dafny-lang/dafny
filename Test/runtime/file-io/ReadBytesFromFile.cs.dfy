// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target:cs "%s" -- "%S/ReadBytesFromFile.data" >> "%t"
// RUN: %diff "%S/ReadBytesFromFile.expect" "%t"

include "./AbstractReadBytesFromFile.dfy"
include "./FileIO.cs.dfy"

module Test refines AbstractTest {
  import FileIO = FileIO_Csharp

  function method ExpectedErrorMessagePrefix(): string {
    "System.ArgumentException: "
  }
}
