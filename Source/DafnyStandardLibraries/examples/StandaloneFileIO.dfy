/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

// Standalone FileIO test that doesn't rely on standard library externs
module StandaloneFileIO {
  
  // Define our own Result type
  datatype Result<T, E> = Success(value: T) | Failure(error: E)
  
  // Define extern methods directly in this module
  method {:extern} ReadBytesFromFile(path: string) 
    returns (result: Result<seq<bv8>, string>)
  
  method {:main} Main() {
    var filename := "Source/DafnyStandardLibraries/examples/StandaloneFileIO.dfy";
    
    var readResult := ReadBytesFromFile(filename);
    match readResult {
      case Success(content) => {
        print "Successfully read ", |content|, " bytes\n";
        print "Standalone FileIO test: PASSED\n";
      }
      case Failure(error) => {
        print "Failed to read file: ", error, "\n";
        print "Standalone FileIO test: FAILED\n";
      }
    }
  }
}
