// Test file for FileIO with Rust target
import Std.FileIO

method Main() {
  // First create a file to read
  var testContent := "Hello, Rust FileIO!";
  var testPath := "test_file.txt";
  
  // Write to file
  var writeResult := FileIO.WriteUTF8ToFile(testPath, testContent);
  if writeResult.Pass? {
    print "Successfully wrote to file\n";
  } else {
    print "Failed to write to file: ", writeResult.error, "\n";
    return;
  }
  
  // Read from file
  var readResult := FileIO.ReadUTF8FromFile(testPath);
  if readResult.Success? {
    print "Successfully read from file: '", readResult.value, "'\n";
  } else {
    print "Failed to read from file: ", readResult.error, "\n";
  }
}
