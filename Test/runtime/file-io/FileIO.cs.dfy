// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%S/FileIO.expect" "%t"

include "./AbstractFileIO.dfy"

module FileIO refines AbstractFileIO {
  export extends AbstractFileIO

  method
    {:extern "Dafny.Helpers", "INTERNAL_ReadBytesFromFile"} {:compile false}
    INTERNAL_ReadBytesFromFile(path: string)
    returns (isError: bool, bytesRead: seq<bv8>, errorMsg: string)

  method
    {:extern "Dafny.Helpers", "INTERNAL_WriteBytesToFile"} {:compile false}
    INTERNAL_WriteBytesToFile(path: string, bytes: seq<bv8>)
    returns (isError: bool, errorMsg: string)
}
