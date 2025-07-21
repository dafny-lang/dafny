// Minimal test file for FileIO with Rust target
module TestFileIO {
  import opened Std.Wrappers
  import Std.FileIOInternalExterns

  // Read a file as UTF-8 text
  method ReadUTF8FromFile(path: string) returns (result: Result<string, string>)
  {
    var isError, bytesRead, errorMsg := FileIOInternalExterns.INTERNAL_ReadBytesFromFile(path);
    if isError {
      return Failure(errorMsg);
    }
    
    // Simple UTF-8 decoding (this is a simplified version)
    var text := "";
    for i := 0 to |bytesRead| {
      text := text + [bytesRead[i] as char];
    }
    return Success(text);
  }

  method Main() {
    var result := ReadUTF8FromFile("test_fileio_minimal.dfy");
    if result.Success? {
      print "File content: ", result.value, "\n";
    } else {
      print "Error reading file: ", result.error, "\n";
    }
  }
}
