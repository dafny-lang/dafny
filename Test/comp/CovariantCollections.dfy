// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cs "%s" > "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  // TODO-RS: Just testing the recent support for covariance in sequneces in C# for now.
  // These also work in Javascript, but hit runtime type errors in Go and still don't
  // compile in Java. Once we have parity in all languages these tests can be
  // relocated to the same Collections.dfy file.
  // Also, it's unfortunate that you can't customize how classes are printed. Perhaps
  // tests of valid Dafny programs should use `expect` and even {:test} now?
  Sequences();
}

trait Number {
  method Print()
}

class Integer extends Number {
  const value: int
  constructor(value: int) {
    this.value := value;
  }
  method Print() {
    print value;
  }
}

method PrintSeq(prefix: string, s: seq<Number>) {
  print prefix, "[";
  var i, sep := 0, "";
  while i < |s| {
    print sep;
    s[i].Print();
    i, sep := i + 1, ", ";
  }
  print "]";
}

method Sequences() {
  var twelve := new Integer(12);
  var seventeen := new Integer(17);
  var fortyTwo := new Integer(42);
  var eightyTwo := new Integer(82);

  var a := [];
  var b: seq<Number> := [seventeen, eightyTwo, seventeen, eightyTwo];
  var c := [twelve, seventeen];

  PrintSeq("Sequences: ", a);
  PrintSeq(" ", b);
  PrintSeq(" ", c);
  print "\n";

  print "  cardinality: ", |a|, " ", |b|, " ", |c|, "\n";
  PrintSeq("  update: ", b[0 := fortyTwo]);
  PrintSeq(" ", c[0 := fortyTwo]);
  print "\n";

  print "  index: ";
  b[0].Print();
  print " ";
  c[0].Print();
  print "\n";

  PrintSeq("  subsequence ([lo..hi]): ", b[1..3]);
  PrintSeq(" ", c[1..2]);
  print "\n";

  PrintSeq("  subsequence ([lo..]): ", b[1..]);
  PrintSeq(" ", c[1..]);
  print "\n";

  PrintSeq("  subsequence ([..hi]): ", b[..3]);
  PrintSeq(" ", c[..2]);
  print "\n";

  PrintSeq("  subsequence ([..]): ", a[..]);
  PrintSeq(" ", b[..]);
  PrintSeq(" ", c[..]);
  print "\n";

  PrintSeq("  concatenation: ", a + b);
  PrintSeq(" ", b + c);
  print "\n";

  print "  prefix: ", a <= b, " ", b <= c, " ", c <= c, "\n";
  print "  proper prefix: ", a < b, " ", b < c, " ", c < c, "\n";
  print "  membership: ", seventeen in a, " ", seventeen in b, " ", seventeen in c, "\n";
}
