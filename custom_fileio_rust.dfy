// Custom FileIO module with Rust implementation

module Wrappers {
  // Simple Result type
  datatype Result<T, E> = Success(value: T) | Failure(error: E)
  
  // Simple Outcome type
  datatype Outcome<E> = Pass | Failure(error: E)
}

module {:extern "FileIOInternalExterns_Impl"} FileIOInternalExterns {
  method {:extern} INTERNAL_ReadBytesFromFile(path: string)
    returns (isError: bool, bytesRead: seq<bv8>, errorMsg: string)

  method {:extern} INTERNAL_WriteBytesToFile(path: string, bytes: seq<bv8>)
    returns (isError: bool, errorMsg: string)
}

module FileIO {
  import opened Wrappers
  import FileIOInternalExterns

  // Read a file as UTF-8 text
  method ReadUTF8FromFile(path: string) returns (result: Result<string, string>)
    decreases *
  {
    var isError, bytesRead, errorMsg := FileIOInternalExterns.INTERNAL_ReadBytesFromFile(path);
    if isError {
      return Result.Failure(errorMsg);
    }
    
    // Simple UTF-8 decoding (this is a simplified version)
    var text := "";
    for i := 0 to |bytesRead| {
      text := text + [bytesRead[i] as char];
    }
    return Result.Success(text);
  }

  // Write UTF-8 text to a file
  method WriteUTF8ToFile(path: string, content: string) returns (result: Outcome<string>)
    decreases *
  {
    // Simple UTF-8 encoding (this is a simplified version)
    var bytes: seq<bv8> := [];
    for i := 0 to |content| {
      bytes := bytes + [content[i] as bv8];
    }
    
    var isError, errorMsg := FileIOInternalExterns.INTERNAL_WriteBytesToFile(path, bytes);
    if isError {
      return Outcome.Failure(errorMsg);
    }
    return Outcome.Pass;
  }

  // Read raw bytes from a file
  method ReadBytesFromFile(path: string) returns (result: Result<seq<bv8>, string>)
    decreases *
  {
    var isError, bytesRead, errorMsg := FileIOInternalExterns.INTERNAL_ReadBytesFromFile(path);
    if isError {
      return Result.Failure(errorMsg);
    }
    return Result.Success(bytesRead);
  }

  // Write raw bytes to a file
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
