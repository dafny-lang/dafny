// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment --spill-translation --allow-deprecation --unicode-char false

// A set used as a set element / map key must hash by content, not by insertion order.
// The cpp backend's set hash was order-dependent, so two equal sets built in different
// orders were treated as distinct.

newtype u8 = x: int | 0 <= x < 256

method Main() {
  var a: set<u8> := {1, 2, 3};
  var b: set<u8> := {3, 2, 1};   // equal to a, different build order
  var outer: set<set<u8>> := {a, b};
  print |outer|, "\n";           // 1

  var m: map<set<u8>, u8> := map[a := 7];
  print b in m, "\n";            // true
}
