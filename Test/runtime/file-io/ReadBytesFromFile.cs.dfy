// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target:cs "%s" -- "%S/ReadBytesFromFile.dfy.data" >> "%t"
// RUN: %diff "%S/ReadBytesFromFile.dfy.expect" "%t"

include "./ReadBytesFromFile.dfy"
include "./FileIO.cs.dfy"

module Test refines AbstractTest {
  import FileIO = FileIO_Csharp

  function method ExpectedErrorMessagePrefix(): string {
    "System.ArgumentException: "
  }
}
