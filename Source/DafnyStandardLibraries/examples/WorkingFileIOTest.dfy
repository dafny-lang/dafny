/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

// Working FileIO test that demonstrates Rust backend FileIO functionality
module WorkingFileIOTest {
  
  // Define our own Result type
  datatype Result<T, E> = Success(value: T) | Failure(error: E)
  
  // Define extern methods directly in this module
  method {:extern} ReadBytesFromFile(path: string) 
    returns (result: Result<seq<bv8>, string>)
  
  method {:main} Main() {
    // Read this source file
    var filename := "Source/DafnyStandardLibraries/examples/WorkingFileIOTest.dfy";
    
    var readResult := ReadBytesFromFile(filename);
    match readResult {
      case Success(content) => {
        print "Successfully read ", |content|, " bytes from ", filename, "\n";
        
        // Verify we read some content
        if |content| > 0 {
          print "FileIO Rust backend test: PASSED\n";
        } else {
          print "FileIO Rust backend test: FAILED (empty file)\n";
        }
      }
      case Failure(error) => {
        print "Failed to read file: ", error, "\n";
        print "FileIO Rust backend test: FAILED\n";
      }
    }
  }
}
