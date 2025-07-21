// Minimal standard library for Rust that avoids ORDINAL

module {:extern} {:dummyImportMember "Dummy__", true} FileIOInternalExterns {
  method {:extern} INTERNAL_ReadBytesFromFile(path: string)
    returns (isError: bool, bytesRead: seq<bv8>, errorMsg: string)

  method {:extern} INTERNAL_WriteBytesToFile(path: string, bytes: seq<bv8>)
    returns (isError: bool, errorMsg: string)
}

// Create the Std namespace structure
module Std {
  module Wrappers {
    datatype Result<T, E> = Success(value: T) | Failure(error: E)
    datatype Outcome<E> = Pass | Failure(error: E)
    datatype Option<T> = Some(value: T) | None
  }
  
  module FileIO {
    import opened Std.Wrappers
    import FileIOInternalExterns

    method ReadUTF8FromFile(path: string) returns (result: Result<string, string>)
      decreases *
    {
      var isError, bytesRead, errorMsg := FileIOInternalExterns.INTERNAL_ReadBytesFromFile(path);
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
      
      var isError, errorMsg := FileIOInternalExterns.INTERNAL_WriteBytesToFile(path, bytes);
      if isError {
        return Outcome.Failure(errorMsg);
      }
      return Outcome.Pass;
    }

    method ReadBytesFromFile(path: string) returns (result: Result<seq<bv8>, string>)
      decreases *
    {
      var isError, bytesRead, errorMsg := FileIOInternalExterns.INTERNAL_ReadBytesFromFile(path);
      if isError {
        return Result.Failure(errorMsg);
      }
      return Result.Success(bytesRead);
    }

    method WriteBytesToFile(path: string, bytes: seq<bv8>) returns (result: Result<(), string>)
      decreases *
    {
      var isError, errorMsg := FileIOInternalExterns.INTERNAL_WriteBytesToFile(path, bytes);
      if isError {
        return Result.Failure(errorMsg);
      }
      return Result.Success(());
    }
  }
}
