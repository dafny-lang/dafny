import Std.FileIO

method Main() {
  var content := FileIO.ReadUTF8FromFile("test_rust_fileio.dfy");
  match content {
    case Success(data) => print data;
    case Failure(error) => print "Error: ", error;
  }
}
