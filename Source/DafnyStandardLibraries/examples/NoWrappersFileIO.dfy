/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

// FileIO test without Wrappers module
module NoWrappersFileIO {
  // Define our own Result type to avoid Wrappers
  datatype Result<T, E> = Success(value: T) | Failure(error: E)

  // Import FileIO directly
  import Std.FileIO

  method {:main} Main() {
    var filename := "Source/DafnyStandardLibraries/examples/NoWrappersFileIO.dfy";
    
    var readResult := FileIO.ReadBytesFromFile(filename);
    match readResult {
      case Success(content) => {
        print "Successfully read ", |content|, " bytes\n";
        print "No Wrappers FileIO test: PASSED\n";
      }
      case Failure(error) => {
        print "Failed to read file: ", error, "\n";
        print "No Wrappers FileIO test: FAILED\n";
      }
    }
  }
}
