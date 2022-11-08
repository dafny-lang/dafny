// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target:java "%s" -- "%S/ReadBytesFromFile.data" >> "%t"
// RUN: %diff "%S/ReadBytesFromFile.expect" "%t"

include "./AbstractReadBytesFromFile.dfy"
include "./FileIO.java.dfy"

module Test refines AbstractTest {
  import FileIO = FileIO_Java

  function method ExpectedErrorMessagePrefix(): string {
    "java.io.IOException: "
  }
}
