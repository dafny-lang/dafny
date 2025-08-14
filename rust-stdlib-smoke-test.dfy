import opened Std.Wrappers
import Std.FileIOInternalExterns

method Main() {
  // Test basic Wrappers functionality
  var opt := Some(42);
  match opt {
    case Some(value) => {
      print "Option contains: ", value, "\n";
    }
    case None =>
      print "Option is empty\n";
  }
  
  var result: Result<int, string> := Success(123);
  match result {
    case Success(value) =>
      print "Result success: ", value, "\n";
    case Failure(error) =>
      print "Result failure: ", error, "\n";
  }

  // Test FileIO functionality
  var isError, bytesRead, errorMsg := FileIOInternalExterns.INTERNAL_ReadBytesFromFile("/local/home/mimayere/dafny2/rust-stdlib-smoke-test.dfy");
  if !isError {
    print "FileIO read successful, got ", |bytesRead|, " bytes\n";
  } else {
    print "FileIO read failed: ", errorMsg, "\n";
  }
}
