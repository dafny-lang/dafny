// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%S/FileIO.expect" "%t"

include "./AbstractFileIO.dfy"

module FileIO_Csharp refines AbstractFileIO {
  export extends AbstractFileIO

  method
    {:extern "Dafny.Helpers", "INTERNAL_ReadBytesFromFile"} {:compile false}
    INTERNAL_ReadBytesFromFile(path: string)
    returns (isError: bool, bytesRead: seq<bv8>, errorMsg: string)
}
