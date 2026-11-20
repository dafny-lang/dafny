// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment --spill-translation --allow-deprecation --unicode-char false

// A set or map used as a set element / map key must hash by content, not by insertion order.

newtype u8 = x: int | 0 <= x < 256

method Main() {
  var a: set<u8> := {1, 2, 3};
  var b: set<u8> := {3, 2, 1};   // equal to a, different build order
  var outer: set<set<u8>> := {a, b};
  print |outer|, "\n";

  var m: map<set<u8>, u8> := map[a := 7];
  print b in m, "\n";

  var c: map<u8, u8> := map[1 := 10, 2 := 20, 3 := 30];
  var d: map<u8, u8> := map[3 := 30, 2 := 20, 1 := 10];   // equal to c, different build order
  var maps: set<map<u8, u8>> := {c, d};
  print |maps|, "\n";

  var n: map<map<u8, u8>, u8> := map[c := 7];
  print d in n, "\n";
}
