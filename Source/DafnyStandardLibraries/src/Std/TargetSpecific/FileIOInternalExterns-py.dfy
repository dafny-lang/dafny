/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

/*
 * Private API - these should not be used elsewhere
 */
// {:compile false} is necessary here since otherwise the translation to Python
// will create a Std_FileIOInternalExterns.py source file as well,
// which the embedded version can't easily override.
module {:extern} {:compile false} Std.PythonFileIOInternalExterns replaces FileIOInternalExterns {
  method {:extern} INTERNAL_ReadBytesFromFile(path: string)
    returns (isError: bool, bytesRead: seq<bv8>, errorMsg: string)

  method {:extern} INTERNAL_WriteBytesToFile(path: string, bytes: seq<bv8>)
    returns (isError: bool, errorMsg: string)
}