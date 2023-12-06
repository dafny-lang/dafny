/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

/**
  * This module provides basic file I/O operations: reading and writing bytes from/to a file.
  * The provided API is intentionally limited in scope and will be expanded later.
  *
  * Where the API accepts file paths as strings, there are some limitations.
  * File paths containing only ASCII characters work identically across languages and platforms;
  * non-ASCII Unicode codepoints may cause different language- or platform-specific behavior.
  *
  * File path symbols including . and .. are allowed.
  */
module Std.FileIO {
  import opened Wrappers
  import FileIOInternalExterns

  export provides ReadBytesFromFile, WriteBytesToFile, Wrappers

  /*
   * Public API
   */

  /**
    * Attempts to read all bytes from the file at the given file path.
    * If an error occurs, a `Result.Failure` value is returned containing an implementation-specific
    * error message (which may also contain a stack trace).
    *
    * NOTE: See the module description for limitations on the path argument.
    */
  method ReadBytesFromFile(path: string) returns (res: Result<seq<bv8>, string>) {
    var isError, bytesRead, errorMsg := FileIOInternalExterns.INTERNAL_ReadBytesFromFile(path);
    return if isError then Failure(errorMsg) else Success(bytesRead);
  }

  /**
    * Attempts to write the given bytes to the file at the given file path,
    * creating nonexistent parent directories as necessary.
    * If an error occurs, a `Result.Failure` value is returned containing an implementation-specific
    * error message (which may also contain a stack trace).
    *
    * NOTE: See the module description for limitations on the path argument.
    */
  method WriteBytesToFile(path: string, bytes: seq<bv8>) returns (res: Result<(), string>) {
    var isError, errorMsg := FileIOInternalExterns.INTERNAL_WriteBytesToFile(path, bytes);
    return if isError then Failure(errorMsg) else Success(());
  }
}
