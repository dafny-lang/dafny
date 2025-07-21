// Test file for FileIO with Rust target
import Std.FileIO

method Main() {
  var s := FileIO.ReadUTF8FromFile("test_fileio.dfy");
  if s.Success? {
    print s.value;
  } else {
    print "Failed to read file: ", s.error;
  }
}
