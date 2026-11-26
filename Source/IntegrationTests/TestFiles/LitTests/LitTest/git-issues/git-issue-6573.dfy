// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s"

// Equal reals with different num/den must hash equal (set/map/multiset).

method Main() {
  var a := new real[1];  // C# stores this default as 0/0
  var zeros: set<real> := {0.0, 0.5 - 0.5, a[0]};
  print "zeros: ", |zeros|, "\n";

  var halves: set<real> := {0.5, 1.0 / 2.0, 2.0 / 4.0};
  print "halves: ", |halves|, "\n";

  var m: map<real, int> := map[0.5 := 1];
  print "lookup: ", (1.0 / 2.0) in m, "\n";

  var ms: multiset<real> := multiset{0.5, 1.0 / 2.0, 2.0 / 4.0};
  print "mult: ", ms[0.5], "\n";
}
