/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module FileIOExamples {
  import Std.FileIO
  import opened Std.Wrappers

  @Test
  method TestFileIOBasic() {
    // Test basic file operations
    var testContent := "Hello, Rust FileIO!";
    var testPath := "test_rust_fileio.txt";

    // Write to file (returns Outcome<string>)
    var writeResult := FileIO.WriteUTF8ToFile(testPath, testContent);
    expect writeResult.Pass?, "Failed to write file: " + writeResult.error;

    // Read from file (returns Result<string, string>)
    var readResult := FileIO.ReadUTF8FromFile(testPath);
    expect readResult.Success?, "Failed to read file: " + readResult.error;
    expect readResult.value == testContent, "File content mismatch";

    print "Rust FileIO test passed!\n";
  }

  @Test
  method TestFileIOBytes() {
    // Test byte operations
    var testBytes: seq<bv8> := [72, 101, 108, 108, 111]; // "Hello" in ASCII
    var testPath := "test_rust_bytes.bin";

    // Write bytes to file (returns Result<(), string>)
    var writeResult := FileIO.WriteBytesToFile(testPath, testBytes);
    expect writeResult.Success?, "Failed to write bytes: " + writeResult.error;

    // Read bytes from file (returns Result<seq<bv8>, string>)
    var readResult := FileIO.ReadBytesFromFile(testPath);
    expect readResult.Success?, "Failed to read bytes: " + readResult.error;
    expect readResult.value == testBytes, "Byte content mismatch";

    print "Rust FileIO bytes test passed!\n";
  }
}
