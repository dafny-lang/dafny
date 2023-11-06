/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

/*
 * Private API - these are intentionally not exported from the module and should not be used elsewhere
 */
module DafnyStdLibs.FileIOInternalExterns {
  method
    {:extern "DafnyStdLibs.FileIOInternalExterns", "INTERNAL_ReadBytesFromFile"}
  INTERNAL_ReadBytesFromFile(path: string)
    returns (isError: bool, bytesRead: seq<bv8>, errorMsg: string)

  method
    {:extern "DafnyStdLibs.FileIOInternalExterns", "INTERNAL_WriteBytesToFile"}
  INTERNAL_WriteBytesToFile(path: string, bytes: seq<bv8>)
    returns (isError: bool, errorMsg: string)
}