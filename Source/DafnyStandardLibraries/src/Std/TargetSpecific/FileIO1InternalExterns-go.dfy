/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

/*
 * Private API - these should not be used elsewhere
 */
@Compile(false)
module
  // This attribute isn't strictly necessary because it's possible
  // to split the implementation of a Dafny module
  // across multiple Go files under the same path.
  // But it makes debugging the translated output a little clearer.
  {:extern}
  {:dummyImportMember "Dummy__", true}
  Std.GoFileIOInternalExterns replaces FileIOInternalExterns {
  method
    {:extern}
    INTERNAL_ReadBytesFromFile(path: string)
    returns (isError: bool, bytesRead: seq<bv8>, errorMsg: string)

  method
    {:extern}
    INTERNAL_WriteBytesToFile(path: string, bytes: seq<bv8>)
    returns (isError: bool, errorMsg: string)
}