include "./FileIO.dfy"

module FileIO_Python refines AbstractFileIO {
  export extends AbstractFileIO

  method
    {:extern "_dafny", "INTERNAL_ReadBytesFromFile"} {:compile false}
    INTERNAL_ReadBytesFromFile(path: string)
    returns (isError: bool, bytesRead: seq<bv8>, errorMsg: string)
}
