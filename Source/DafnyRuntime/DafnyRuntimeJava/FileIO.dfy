/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

/*
 * Private API - these should not be used elsewhere
 */
module Std.JavaFileIOInternalExterns replaces FileIOInternalExterns {
  import opened JavaInternal

  method INTERNAL_ReadBytesFromFile(path: string)
    returns (isError: bool, bytesRead: seq<bv8>, errorMsg: string) {
    var r1, r2, r3 := FileIO.INTERNAL_ReadBytesFromFile(path);
    return r1, r2, r3;
  }

  method INTERNAL_WriteBytesToFile(path: string, bytes: seq<bv8>)
    returns (isError: bool, errorMsg: string) {
    var r1, r2 := FileIO.INTERNAL_WriteBytesToFile(path, bytes);
    return r1, r2;
  }

}

/**
This module is so we can avoid having a __default class in Java
*/
module JavaInternal {
  class FileIO {
      static method
        {:extern "Std.FileIOInternalExterns.FileIO", "INTERNAL_ReadBytesFromFile"}
      INTERNAL_ReadBytesFromFile(path: string)
        returns (isError: bool, bytesRead: seq<bv8>, errorMsg: string)

      static method
        {:extern "Std.FileIOInternalExterns.FileIO", "INTERNAL_WriteBytesToFile"}
      INTERNAL_WriteBytesToFile(path: string, bytes: seq<bv8>)
        returns (isError: bool, errorMsg: string)
  }
}