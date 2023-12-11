/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

/*
 * Private API - these should not be used elsewhere
 */
module Std.CSharpFileIOInternalExterns replaces FileIOInternalExterns {

  // TODO Container override in {:extern} is not being picked up
  method
    {:extern "Std.CSharpFileIOInternalExterns.FileIO", "INTERNAL_ReadBytesFromFile"}
  INTERNAL_ReadBytesFromFile(path: string)
    returns (isError: bool, bytesRead: seq<bv8>, errorMsg: string)

  method
    {:extern "Std.CSharpFileIOInternalExterns.FileIO", "INTERNAL_WriteBytesToFile"}
  INTERNAL_WriteBytesToFile(path: string, bytes: seq<bv8>)
    returns (isError: bool, errorMsg: string)
}