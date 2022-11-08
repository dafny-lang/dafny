// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target:cs "%s" -- "%t.data" >> "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %diff "%s.data.expect" "%t.data"

include "../../libraries/src/Wrappers.dfy"

import opened Wrappers

method
  {:extern "Dafny.Helpers", "INTERNAL_WriteBytesToFile"}
  {:compile false}
  INTERNAL_WriteBytesToFile(path: string, bytes: seq<bv8>)
  returns (isError: bool, errorMsg: string)

method WriteBytesToFile(path: string, bytes: seq<bv8>)
  returns (res: Result<(), string>)
{
  var isError, errorMsg := INTERNAL_WriteBytesToFile(path, bytes);
  return if isError then Failure(errorMsg) else Success(());
}

method Main(args: seq<string>) {
  {
    var str := "Hello world\nGoodbye\n";
    var bytes := seq(|str|, i requires 0 <= i < |str| => str[i] as bv8);

    expect |args| == 2;
    var dataFilePath := args[1];

    var res := WriteBytesToFile(dataFilePath, bytes);
    expect res.Success?;
  }

  {
    var res := WriteBytesToFile("", []);
    expect res.Failure?;
    expect "System.ArgumentException: " <= res.error;
  }
}
