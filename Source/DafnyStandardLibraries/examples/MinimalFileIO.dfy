/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

// Minimal FileIO test using extern functions directly
module MinimalFileIO {
  import opened Std.Wrappers

  // Use the FileIO extern functions directly to avoid complex standard library dependencies
  module {:extern} FileIOInternalExterns {
    method {:extern} INTERNAL_ReadBytesFromFile(path: string)
      returns (isError: bool, bytesRead: seq<bv8>, errorMsg: string)
  }

  method {:main} Main() {
    // Try to read this file directly using the extern function
    var filename := "Source/DafnyStandardLibraries/examples/MinimalFileIO.dfy";
    
    var isError, bytesRead, errorMsg := FileIOInternalExterns.INTERNAL_ReadBytesFromFile(filename);
    
    if isError {
      print "Failed to read file: ", errorMsg, "\n";
      print "Minimal FileIO test: FAILED\n";
    } else {
      print "Successfully read ", |bytesRead|, " bytes from ", filename, "\n";
      print "Minimal FileIO test: PASSED\n";
    }
  }
}
