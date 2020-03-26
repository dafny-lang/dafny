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

}

class Integer extends Number {
  const value: int
  constructor(value: int) {
    this.value := value;
  }
}

method Sequences() {
  var twelve := new Integer(12);
  var seventeen := new Integer(17);
  var fortyTwo := new Integer(42);
  var eightyTwo := new Integer(82);

  var a := [];
  var b : seq<Number> := [seventeen, eightyTwo, seventeen, eightyTwo];
  var c := [twelve, seventeen];
  print "Sequences: ", a, " ", b, " ", c, "\n";
  print "  cardinality: ", |a|, " ", |b|, " ", |c|, "\n";
  print "  update: ", b[0 := fortyTwo], " ", c[0 := fortyTwo], "\n";
  print "  index: ", b[0], " ", c[0], "\n";
  print "  subsequence ([lo..hi]): ", b[1..3], " ", c[1..2], "\n";
  print "  subsequence ([lo..]): ", b[1..], " ", c[1..], "\n";
  print "  subsequence ([..hi]): ", b[..3], c[..1], "\n";
  print "  subsequence ([..]): ", a[..], " ", b[..], " ", c[..], "\n";
  print "  concatenation: ", a + b, " ", b + c, "\n";
  print "  prefix: ", a <= b, " ", b <= c, " ", c <= c, "\n";
  print "  proper prefix: ", a < b, " ", b < c, " ", c < c, "\n";
  print "  membership: ", seventeen in a, " ", seventeen in b, " ", seventeen in c, "\n";
}
