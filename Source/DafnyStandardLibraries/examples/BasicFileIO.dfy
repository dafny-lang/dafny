/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

// Basic FileIO test for Rust backend
module BasicFileIO {
  import opened Std.Wrappers
  import Std.FileIO

  method {:main} Main() {
    var filename := "Source/DafnyStandardLibraries/examples/BasicFileIO.dfy";
    
    var readResult := FileIO.ReadBytesFromFile(filename);
    match readResult {
      case Success(content) => {
        print "Successfully read ", |content|, " bytes\n";
        print "Basic FileIO test: PASSED\n";
      }
      case Failure(error) => {
        print "Failed to read file: ", error, "\n";
        print "Basic FileIO test: FAILED\n";
      }
    }
  }
}
