import Std.FileIO
import opened Std.Wrappers

method Main() {
  // Test basic FileIO functionality
  var testContent := "Hello, Rust FileIO!";
  var testFile := "test_output.txt";
  
  // Test writing UTF8 to file
  var writeResult := FileIO.WriteUTF8ToFile(testFile, testContent);
  match writeResult {
    case Success(_) => print "Successfully wrote to file\n";
    case Failure(error) => print "Write failed: ", error, "\n";
  }
  
  // Test reading UTF8 from file
  var readResult := FileIO.ReadUTF8FromFile(testFile);
  match readResult {
    case Success(content) => {
      print "Successfully read from file: ", content, "\n";
      expect content == testContent;
    }
    case Failure(error) => print "Read failed: ", error, "\n";
  }
  
  print "FileIO test completed\n";
}
