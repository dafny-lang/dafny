// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=cs "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=js "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=go "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

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
