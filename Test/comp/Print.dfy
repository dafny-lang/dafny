// NONUNIFORM: https://github.com/dafny-lang/dafny/issues/4108
// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment --unicode-char:false

// Python salts hashes so they are not deterministic.

method Main() {
  PrintString();
}

method PrintString() {
  print "Strings in collections:\n";
  print "  ", ["abc", "def"], "\n";
  print "  ", [["abc", "def"]], "\n";
  print "  ", {"abc", "def"}, "\n";
  print "  ", [['a', 'b', 'c'], ['d', 'e', 'f']], "\n";
  var a : seq<seq<char>> := [[]];
  print "  ", a, "\n";
  var b : seq<char>;
  print "  ", [b], "\n";
  print "  ", [seq(5, x => 'a')], "\n";
}
