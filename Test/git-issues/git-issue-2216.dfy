// RUN: %baredafny run %args --no-verify --target=cs "%s" >> "%t"

const REPEAT := 100_000

method NoPhysicalEqualityOnSequences(s: seq<int>) {
  for i := 0 to REPEAT {
    var b := s == s; // No physical equality makes this take linear time
  }
}

method EqualityAtLeastLinear(s: seq<int>) {
  var s0 := [0] + s;
  var s1 := [1] + s;
  for i := 0 to REPEAT {
    var b := s0 == s1; // Full sequence copy makes this linear time
  }
}

method ElementsCopiedToPerformLengthCheck(s: seq<int>) {
  var empty: seq<int> := [];
  for i := 0 to REPEAT {
    var b := [] <= s;
  }
}

method Main() {
  var s := seq(10_000_000, _ => 0);

  print "ElementsCopiedToPerformLengthCheck... ";
  ElementsCopiedToPerformLengthCheck(s);
  print "done.\n";

  print "EqualityAtLeastLinear... ";
  EqualityAtLeastLinear(s);
  print "done.\n";

  print "NoPhysicalEqualityOnSequences... ";
  NoPhysicalEqualityOnSequences(s);
  print "done.\n";
}
