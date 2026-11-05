// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --enforce-determinism --spill-translation --allow-deprecation --unicode-char false

newtype i32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype List<T> = Nil | Cons(head: T, tail: List<T>)
datatype Opt<T> = None | Some(v: T)
datatype Seqs<T> = NoSeq | Seq(s: seq<T>)
datatype Fn = NoFn | Fn(f: i32 -> i32, fs: seq<i32 -> i32>, n: i32)
datatype Box = Box(o: Opt<i32 -> i32>)
datatype Fs = Fs(s: seq<i32 -> i32>)

method IsNone<T>(o: Opt<T>) returns (b: bool) {
  b := o == None;
}

// C++ keywords as member names.
class Keywords {
  const long: i32
  var short: i32
  const register := 3 as i32
  static const double := 4 as i32
  constructor() {
    long := 1;
    short := 2;
  }
}

method Main() {
  // Fields of a type-parameter type are compared and hashed.
  var a: List<i32> := Cons(1, Nil);
  var b: List<i32> := Cons(2, Nil);
  print a == b, " ", a == Cons(1, Nil), " ", a != b, " ", |{a, b}|, "\n";

  // A function as type argument: only comparisons with a nullary constructor.
  var inc: i32 -> i32 := n => if n < 0x7fff_ffff then n + 1 else n;
  var o: Opt<i32 -> i32> := Some(inc);
  var none: Opt<i32 -> i32> := None;
  print o == None, " ", None == none, " ", o != None, "\n";
  var isNone := IsNone(o);
  var isNoneToo := IsNone(none);
  print isNone, " ", isNoneToo, "\n";
  var s: Seqs<i32 -> i32> := Seq([inc]);
  print s == NoSeq, "\n";

  // Function-typed fields of a non-generic datatype.
  var f := Fn(inc, [inc], 3);
  print f == NoFn, " ", f.n, "\n";

  // Comparisons with a value that holds no function, below the top level.
  var box := Box(Some(inc));
  print box == Box(None), " ", Box(None) == Box(None), "\n";
  var nested: Opt<Opt<i32 -> i32>> := Some(Some(inc));
  print nested == Some(None), " ", nested == None, "\n";
  var fs: seq<i32 -> i32> := [inc];
  print fs == [], " ", Fs(fs) == Fs([]), "\n";

  var k := new Keywords();
  print k.long, " ", k.short, " ", k.register, " ", Keywords.double, "\n";
}
