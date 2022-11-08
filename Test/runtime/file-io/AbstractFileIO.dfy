// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "../../libraries/src/Wrappers.dfy"

abstract module AbstractFileIO {
  import opened Wrappers

  export provides ReadBytesFromFile, WriteBytesToFile, Wrappers

  method ReadBytesFromFile(path: string) returns (res: Result<seq<bv8>, string>) {
    var isError, bytesRead, errorMsg := INTERNAL_ReadBytesFromFile(path);
    return if isError then Failure(errorMsg) else Success(bytesRead);
  }

  method WriteBytesToFile(path: string, bytes: seq<bv8>) returns (res: Result<(), string>)
  {
    var isError, errorMsg := INTERNAL_WriteBytesToFile(path, bytes);
    return if isError then Failure(errorMsg) else Success(());
  }

  method INTERNAL_ReadBytesFromFile(path: string)
    returns (isError: bool, bytesRead: seq<bv8>, errorMsg: string)

  method INTERNAL_WriteBytesToFile(path: string, bytes: seq<bv8>)
    returns (isError: bool, errorMsg: string)
}
