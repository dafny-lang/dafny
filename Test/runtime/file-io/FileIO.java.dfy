include "./FileIO.dfy"

module FileIO_Java refines AbstractFileIO {
  export extends AbstractFileIO

  method
    {:extern "dafny.Helpers", "INTERNAL_ReadBytesFromFile"} {:compile false}
    INTERNAL_ReadBytesFromFile(path: string)
    returns (isError: bool, bytesRead: seq<bv8>, errorMsg: string)
}
