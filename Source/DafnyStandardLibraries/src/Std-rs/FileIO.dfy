/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "Wrappers.dfy"

module Std.FileIO {
  import opened Wrappers
  import FileIOInternalExterns

  method ReadBytesFromFile(path: string) returns (res: Result<seq<bv8>, string>)
  {
    var isError, bytesRead, errorMsg := FileIOInternalExterns.INTERNAL_ReadBytesFromFile(path);
    if isError {
      res := Failure(errorMsg);
    } else {
      res := Success(bytesRead);
    }
  }

  method WriteBytesToFile(path: string, bytes: seq<bv8>) returns (res: Result<(), string>)
  {
    var isError, errorMsg := FileIOInternalExterns.INTERNAL_WriteBytesToFile(path, bytes);
    if isError {
      res := Failure(errorMsg);
    } else {
      res := Success(());
    }
  }

  method ReadUTF8FromFile(path: string) returns (res: Result<string, string>)
  {
    var bytesResult := ReadBytesFromFile(path);
    match bytesResult {
      case Success(bytes) =>
        // Simple conversion from bytes to string (assuming UTF-8)
        var chars := seq(|bytes|, i requires 0 <= i < |bytes| => bytes[i] as char);
        res := Success(chars);
      case Failure(error) =>
        res := Failure(error);
    }
  }

  method WriteUTF8ToFile(path: string, content: string) returns (res: Result<(), string>)
  {
    // Simple conversion from string to bytes (only works for ASCII)
    var bytes := seq(|content|, i requires 0 <= i < |content| => 
      if content[i] as int <= 255 then content[i] as bv8 else 63 as bv8); // Use '?' for non-ASCII
    res := WriteBytesToFile(path, bytes);
  }
}
