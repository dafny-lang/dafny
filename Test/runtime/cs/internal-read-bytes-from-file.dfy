// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target:cs "%s" -- "%s.data" >> "%t"
// RUN: %diff "%s.expect" "%t"

include "../../libraries/src/Wrappers.dfy"

import opened Wrappers

method
  {:extern "Dafny.Helpers", "INTERNAL_ReadBytesFromFile"}
  {:compile false}
  INTERNAL_ReadBytesFromFile(path: string)
  returns (isError: bool, bytesRead: seq<bv8>, errorMsg: string)

method ReadBytesFromFile(path: string)
  returns (res: Result<seq<bv8>, string>)
{
  var isError, bytesRead, errorMsg := INTERNAL_ReadBytesFromFile(path);
  return if isError then Failure(errorMsg) else Success(bytesRead);
}

method Main(args: seq<string>) {
  {
    var expectedStr := "Hello world\nGoodbye\n";
    var expectedBytes := seq(|expectedStr|, i requires 0 <= i < |expectedStr| => expectedStr[i] as bv8);

    expect |args| == 2;
    var dataFilePath := args[1];

    var res := ReadBytesFromFile(dataFilePath);
    expect res.Success?;
    expect res.value == expectedBytes;
  }

  {
    var res := ReadBytesFromFile("");
    expect res.Failure?;
    expect "System.ArgumentException: " <= res.error;
  }
}
