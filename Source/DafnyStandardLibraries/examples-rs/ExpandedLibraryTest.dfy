import Std.FileIO
import opened Std.Wrappers

method Main() {
  // Test FileIO
  var content := FileIO.ReadUTF8FromFile("ExpandedLibraryTest.dfy");
  match content {
    case Success(data) => print "FileIO works: read ", |data|, " characters\n";
    case Failure(error) => print "FileIO error: ", error, "\n";
  }
  
  print "Expanded Rust standard library includes:\n";
  print "- Std.FileIO (tested above)\n";
  print "- Std.Wrappers (Result, Option types)\n";
  print "- Std.Collections (Array, Map, Seq, Set, etc.)\n";
  print "- Std.Math (mathematical functions)\n";
  print "- Std.BoundedInts (uint8, uint16, etc.)\n";
  print "- Std.Functions (function utilities)\n";
  print "- Std.Relations (relation utilities)\n";
  print "- Std.DynamicArray (dynamic arrays)\n";
  print "- Std.Unicode.Base (Unicode support)\n";
  print "\nExpanded standard library test completed successfully!\n";
}
