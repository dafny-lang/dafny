// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target:py "%s" -- "%s.data" >> "%t"
// RUN: %diff "%s.expect" "%t"

include "../../libraries/src/Wrappers.dfy"

import opened Wrappers

method
  // {:extern "Dafny.Helpers", "INTERNAL_ReadBytesFromFile"}  // C#
  // {:extern "dafny.Helpers", "INTERNAL_ReadBytesFromFile"}  // Java
  // {:extern "_dafny", "INTERNAL_ReadBytesFromFile"}  // Javascript
  {:extern "_dafny", "INTERNAL_ReadBytesFromFile"}  // Python
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
    var expectedBytes := seq(|expectedStr|, i requires 0 <= i < |expectedStr| => expectedStr[i] as int);

    expect |args| == 2;
    var dataFilePath := args[1];

    var res := ReadBytesFromFile(dataFilePath);
    expect res.Success?, res.error;
    
    var readBytes := seq(|res.value|, i requires 0 <= i < |res.value| => res.value[i] as int);
    // print "readBytes: ";
    // print readBytes;
    // print "\n";
    // print "expectedBytes: ";
    // print expectedBytes;
    // print "\n";
    expect readBytes == expectedBytes;
  }

  {
    var res := ReadBytesFromFile("");
    expect res.Failure?;
    expect
        || ("System.ArgumentException: " <= res.error)  // C#/.NET
        || ("java.io.IOException: " <= res.error)  // Java
        || ("Error: ENOENT" <= res.error)  // Javascript
        || ("[Errno 2]" <= res.error)  // Python
        , "unexpected error message: " + res.error;
  }
}
