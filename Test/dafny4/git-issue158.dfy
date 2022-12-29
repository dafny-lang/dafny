// RUN: %baredafny run %args "%s" > "%t"
// RUN: %dafny /compile:3 /optimize "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
// See https://github.com/dafny-lang/dafny/issues/508

class Class { }

newtype byte = x | 0 <= x < 256

datatype Record<G> = Make(0:Class?, 1:G, 2:Class, 3:int, 4:byte)

method Main()
{
  var a1 := new Class;
  var a2 := new Class;
  var a3 := new Class;
  var c: map<Record<Class?>,real> := map[
                Make(null,null,a1,5,10) := 0.8,
                Make(null,null,a2,4,11) := 0.1,
                Make(null,null,a3,8,12) := 0.1
                ];
  print map r | r in c && r.4 == 10 :: c[r], "\n";
  print map r | r in c && r.4 == 11 :: c[r], "\n";
  print map r | r in c && r.4 == 12 :: c[r], "\n";
  More(null);
  EvenMore(null);
  AndThenSome(null);
  Compare();
  In();
}

method More(n: Class?)
{
  var x := (5,n);
  var y := (5,n,2);
  var S := {x};
  var S' := {y};
  print x, "\n";
  print y, "\n";
  print S, "\n";
  print S', "\n";
}

method EvenMore(n: Class?)
{
  print {n}, "\n";
  print [n], "\n";
  var empty: multiset<Class?> := multiset{};
  print empty, " ", multiset{n}, " ", multiset{n,n}, "\n";
  print map[5 := n], "\n";
  print map[n := 5], "\n";
}

method AndThenSome(n: Class?)
{
  var A := {n};
  var B := multiset{n};
  var C := [n];
  var D := map[n := n];
  // the following will cause hashcodes to be computed for A, B, C, and D
  print {A}, " ", multiset{A}, " ", [A], " ", map[A := A], "\n";
  print {B}, " ", multiset{B}, " ", [B], " ", map[B := B], "\n";
  print {C}, " ", multiset{C}, " ", [C], " ", map[C := C], "\n";
  print {D}, " ", multiset{D}, " ", [D], " ", map[D := D], "\n";
}

datatype CmpRecord<G> = Cmp(a: object?, g: G)

method Compare() {
  var o := new object;
  var c := new Class;
  var r0: CmpRecord<Class?> := Cmp(null, null);
  var r1: CmpRecord<Class?> := Cmp(o, c);
  print r0==r1, " ", r1==r0, " ", r0==r0, " ", r1==r1, "\n";

  var s := [c, null];
  print c in s, " ", null in s, " ", o in s, "\n";
  var t := [2, 3, 5];
  print 3 in t, " ", 4 in t, "\n";
  var u := [false, false];
  print false in u, " ", true in u, "\n";
}

method In() {
  var o: Class? := new Class;
  var c := new Class;
  var s: seq<Class> := [];
  print o in s, "\n";
  print o == c, " ", c == o, "\n";
  print [o] == [c], " ", [c] == [o], "\n";
  print [o] == [o], " ", [c] == [c], "\n";
}
