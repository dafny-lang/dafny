// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment --spill-translation --allow-deprecation --unicode-char false

newtype i8 = x: int | -128 <= x < 128
newtype i32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype u32 = x: int | 0 <= x < 0x1_0000_0000

// Field names that are C++ keywords
datatype R = R(union: u32, virtual: bool)
datatype M = A(union: u32) | B(virtual: bool)

// Unnamed constructor fields
datatype U = Leaf(u32) | Node(u32, bool)

method Main() {
  // Euclidean division and modulus on signed native types
  var a: i8 := -128;
  var b: i8 := -127;
  var c: i8 := -3;
  print (a / 3) as i32, " ", (a / c) as i32, " ", (b % 3) as i32, " ", (b % c) as i32, " ", ((-7 as i8) / 3) as i32, " ", ((-7 as i8) % 3) as i32, "\n";
  var e: i32 := -0x8000_0000;
  print e / 7, " ", e / -7, " ", (e + 1) % 7, " ", (e + 1) % -7, "\n";

  // Superset and disjointness
  var s: set<u32> := {1, 2, 3};
  var t: set<u32> := {1, 2};
  print s >= t, " ", s > t, " ", t >= s, " ", s > s, " ", s >= s, " ", t !! {5}, " ", t !! s, "\n";

  // Sequence and string prefix
  var p: seq<u32> := [1, 2];
  var q: seq<u32> := [1, 2, 3];
  print p <= q, " ", p < q, " ", q <= p, " ", p < p, " ", "ab" < "abc", " ", "abc" <= "ab", "\n";

  // Tuples as set elements and map keys
  var ts: set<(u32, bool)> := {(1, true), (2, false)};
  var tm: map<(u32, bool), u32> := map[(1, true) := 10];
  print (1, true) in ts, " ", (1, false) in ts, " ", tm[(1, true)], "\n";

  // Keyword field names
  var r := R(4, true);
  var m := A(5);
  var n := B(false);
  print r.union, " ", r.virtual, " ", m.union, " ", n.virtual, "\n";

  // Unnamed fields, constructed and matched
  var u := Node(9, true);
  match u {
    case Leaf(x) => print "leaf ", x, "\n";
    case Node(x, y) => print "node ", x, " ", y, "\n";
  }
}
