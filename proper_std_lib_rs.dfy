// Proper standard library for Rust that avoids ORDINAL

module StdWrappers {
  datatype Result<T, E> = Success(value: T) | Failure(error: E)
  datatype Outcome<E> = Pass | Failure(error: E)
}

module {:extern "FileIOInternalExterns_Impl"} StdFileIOInternalExterns {
  method {:extern} INTERNAL_ReadBytesFromFile(path: string)
    returns (isError: bool, bytesRead: seq<bv8>, errorMsg: string)

  method {:extern} INTERNAL_WriteBytesToFile(path: string, bytes: seq<bv8>)
    returns (isError: bool, errorMsg: string)
}

module Std {
  module Wrappers {
    import opened StdWrappers
    export provides Result, Outcome
  }
  
  module FileIO {
    import opened StdWrappers
    import StdFileIOInternalExterns

    method ReadUTF8FromFile(path: string) returns (result: Result<string, string>)
      decreases *
    {
      var isError, bytesRead, errorMsg := StdFileIOInternalExterns.INTERNAL_ReadBytesFromFile(path);
      if isError {
        return Result.Failure(errorMsg);
      }
      
      var text := "";
      for i := 0 to |bytesRead| {
        text := text + [bytesRead[i] as char];
      }
      return Result.Success(text);
    }

    method WriteUTF8ToFile(path: string, content: string) returns (result: Outcome<string>)
      decreases *
    {
      var bytes: seq<bv8> := [];
      for i := 0 to |content| {
        if content[i] as int <= 255 {
          bytes := bytes + [content[i] as bv8];
        } else {
          bytes := bytes + [63 as bv8]; // '?' for unsupported chars
        }
      }
      
      var isError, errorMsg := StdFileIOInternalExterns.INTERNAL_WriteBytesToFile(path, bytes);
      if isError {
        return Outcome.Failure(errorMsg);
      }
      return Outcome.Pass;
    }

    method ReadBytesFromFile(path: string) returns (result: Result<seq<bv8>, string>)
      decreases *
    {
      var isError, bytesRead, errorMsg := StdFileIOInternalExterns.INTERNAL_ReadBytesFromFile(path);
      if isError {
        return Result.Failure(errorMsg);
      }
      return Result.Success(bytesRead);
    }

    method WriteBytesToFile(path: string, bytes: seq<bv8>) returns (result: Result<(), string>)
      decreases *
    {
      var isError, errorMsg := StdFileIOInternalExterns.INTERNAL_WriteBytesToFile(path, bytes);
      if isError {
        return Result.Failure(errorMsg);
      }
      return Result.Success(());
    }
  }
}
