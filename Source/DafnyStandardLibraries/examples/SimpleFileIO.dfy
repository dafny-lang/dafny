/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

// A simple FileIO test for Rust backend that avoids JSON modules
module SimpleFileIO {
  import opened Std.Wrappers
  import Std.FileIO

  method {:main} Main() {
    // Try to read a simple file
    var filename := "Source/DafnyStandardLibraries/examples/SimpleFileIO.dfy";
    
    var readResult := FileIO.ReadBytesFromFile(filename);
    match readResult {
      case Success(content) => {
        print "Successfully read ", |content|, " bytes from ", filename, "\n";
        print "FileIO test: PASSED\n";
      }
      case Failure(error) => {
        print "Failed to read file: ", error, "\n";
        print "FileIO test: FAILED\n";
      }
    }
  }
}
