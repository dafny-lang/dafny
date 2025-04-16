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
  import Unicode.Utf8EncodingForm
  import Strings
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
  
  /**
    * Attempts to read a text file and convert its contents to a string.
    * The file must contain valid UTF-8 encoded text.
    *
    * Parameters:
    * - fileName: string - The path to the file to read
    *
    * Returns:
    * - Result<string, string> - On success, returns the file contents as a string.
    *   On failure, returns an error message describing what went wrong.
    *
    * Error cases:
    * - File does not exist or cannot be accessed
    * - File content is not valid UTF-8
    * - File contains characters that cannot be represented as UTF-16
    *
    * Example:
    * ```dafny
    * var result := FileIO.ReadFile("example.txt");
    * if result.IsFailure() {
    *   print "Error reading file: ", result.error;
    * } else {
    *   print "File contents: ", result.value;
    * }
    * ```
    */
  method ReadFile(fileName: string) returns (r: Result<string, string>) {
    var bytes :- FileIO.ReadBytesFromFile(fileName);
    if !Utf8EncodingForm.IsWellFormedCodeUnitSequence(bytes) {
      return Failure("Byte sequence of file '" + fileName + "' is not well formed UTF8");
    }
    var x := Utf8EncodingForm.DecodeCodeUnitSequence(bytes);
    if i :| 0 <= i < |x| && !(x[i] < 1 << 16) {
      return Failure("index " + Strings.OfInt(i) + " is not a valid char");
    }
    var s := seq(|x|, i requires 0 <= i < |x| => x[i] as char);
    return Success(s);
  }

  /**
  * Attempts to write a string to a file using UTF-8 encoding.
  * Creates the file if it doesn't exist, or overwrites it if it does.
  * Creates any necessary parent directories.
  *
  * Parameters:
  * - fileName: string - The path where the file should be written
  * - content: string - The string content to write to the file
  *
  * Returns:
  * - Outcome<string> - On success, returns Pass.
  *   On failure, returns an error message describing what went wrong.
  *
  * Error cases:
  * - Cannot create or write to the file (permissions, disk space, etc.)
  * - The content contains characters that cannot be encoded as valid UTF-8 scalar values
  *
  * Example:
  * ```dafny
  * var result := WriteFile("example.txt", "Hello, World!");
  * if result.IsFailure() {
  *   print "Error writing file: ", result.error;
  * } else {
  *   print "File written successfully";
  * }
  * ```
  */
  @IsolateAssertions
  method WriteFile(fileName: string, content: string) returns (r: Outcome<string>)
  {
    if i :| 0 <= i < |content| && !(
              && (0 <= content[i] as bv24 <= 0x10FFFF)
              && (content[i] as bv24 < Utf8EncodingForm.Base.HIGH_SURROGATE_MIN || content[i] as bv24 > Utf8EncodingForm.Base.HIGH_SURROGATE_MAX)
              && (content[i] as bv24 < Utf8EncodingForm.Base.LOW_SURROGATE_MIN || content[i] as bv24 > Utf8EncodingForm.Base.LOW_SURROGATE_MAX)) {
      return Fail("At index " + Strings.OfInt(i) + ", the character cannot be encoded as a scalar value");
    }

    var bytes := Utf8EncodingForm.EncodeScalarSequence(
      seq(|content|, i requires 0 <= i < |content| => content[i] as bv24 as Utf8EncodingForm.Base.ScalarValue)
    );

    var writeResult := FileIO.WriteBytesToFile(fileName, bytes);
    if writeResult.IsFailure() {
      return Fail("Failed to write to file '" + fileName + "': " + writeResult.error);
    }

    return Pass;
  }
}
