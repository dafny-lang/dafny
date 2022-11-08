include "../../libraries/src/Wrappers.dfy"

abstract module AbstractFileIO {
  import opened Wrappers

  export provides ReadBytesFromFile, Wrappers

  method ReadBytesFromFile(path: string) returns (res: Result<seq<bv8>, string>) {
    var isError, bytesRead, errorMsg := INTERNAL_ReadBytesFromFile(path);
    return if isError then Failure(errorMsg) else Success(bytesRead);
  }

  method INTERNAL_ReadBytesFromFile(path: string)
    returns (isError: bool, bytesRead: seq<bv8>, errorMsg: string)
}
