/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

/*
 * Direct Rust implementation of FileIO - bypasses the replaces mechanism
 */
module {:extern "FileIOInternalExterns"} Std.FileIOInternalExterns {
  method {:extern "INTERNAL_ReadBytesFromFile"} INTERNAL_ReadBytesFromFile(path: string)
    returns (isError: bool, bytesRead: seq<bv8>, errorMsg: string)

  method {:extern "INTERNAL_WriteBytesToFile"} INTERNAL_WriteBytesToFile(path: string, bytes: seq<bv8>)
    returns (isError: bool, errorMsg: string)
}
