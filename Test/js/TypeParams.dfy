// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cs "%s" > "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:js "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

datatype Color = Orange | Pink | Teal
type Six = x | x <= 6
newtype Even = x | x % 2 == 0

// types with non-standard (which essentially means non-0) initializers:
type PinkColor = c: Color | c != Orange witness Pink
type Eight = x | 8 <= x witness 19
newtype Odd = x | x % 2 == 1 witness -3

class MyClass {
  var f: int
}
type ReallyJustANullableMyClass = c: MyClass? | true

method Main() {
  Standard<set<Color>>();
  Tp();
  Direct();
}

method Standard<T(0)>() {
  var a: int := Gimmie();
  var b: Six := Gimmie();
  var c: Even := Gimmie();
  var d: bool := Gimmie();
  var e: Color := Gimmie();
  var f: real := Gimmie();
  var g: T := Gimmie();
  print a, " ", b, " ", c, " ", d, " ", e, " ", f, " ", g, "\n";

  // nullable reference types
  var x0: object? := Gimmie();
  var x1: array?<bool> := Gimmie();
  var x2: array3?<int> := Gimmie();
  var x3: MyClass? := Gimmie();
  var x4: ReallyJustANullableMyClass := Gimmie();
  print x0, " ", x1, " ", x2, " ", x3, " ", x4, "\n";

  // collections
  var s0: set<real> := Gimmie();
  var s1: multiset<real> := Gimmie();
  var s2: seq<real> := Gimmie();
  var s3: map<real,Color> := Gimmie();
  var s4: iset<real> := Gimmie();
  var s5: imap<real,Color> := Gimmie();
  print s0, " ", s1, " ", s2, " ", s3, " ", s4, " ", s5, "\n";

  // arrows
  var k0: real --> bool := Gimmie();
  var k1: real ~> bool := Gimmie();
  var k2: () --> int := Gimmie();
  var k3: (Color,set<bv12>) --> bv20 := Gimmie();
  print k0, " ", k1, " ", k2, " ", k3, "\n";  // these functions will print as "null" (sigh)
}

method Gimmie<R(0)>() returns (r: R) { }

// ---------- type parameters ----------

method Tp() {
  var c := new Cl<int, seq<bool>>();
  c.Print();
  var d := new Cl<bool, Color>();
  d.Print();
  var n: NonemptyList<bv7> := Gimmie();
  print n, "\n";
}

datatype Dt<G> = D0(G) | D1(G)

class Cl<X(==,0),Y(0)> {
  var x: X
  var y: Y
  var u: set<X>

  constructor () {
  }

  method Print() {
    print x, " ", y, " ", u, " ";
    var w: X;
    var d: Dt<X>;
    print w, " ", d, "\n";
  }
}

// ---------- direct default values ----------

codatatype IList<G> = ICons(G, IList<G>) | INil
codatatype Stream<G> = Next(G, Stream<G>)
type EmptyList<G> = xs: IList<G> | !xs.ICons? witness INil
type AlwaysNothing = xs: IList<()> | xs != INil witness FauxEvva(())

datatype NonemptyList<G> = Atom(G) | NCons(G, NonemptyList<G>)
codatatype NonemptyCoList<G> = CoAtom(G) | CoNCons(G, NonemptyList<G>)

function method FauxEvva<G>(g: G): IList<G> {
  ICons(g, FauxEvva(g))
}
function method FullStreamAhead<G>(g: G): Stream<G> {
  Next(g, FullStreamAhead(g))
}

method Direct() {
  var s0: IList<int>;
  var s1: IList<bool>;
  var s2: Stream<real>;
  var s3: EmptyList<Color>;
  var s4: AlwaysNothing;
  // print s0, " ", s1, " ", s2, " ";
  print s3, " ", s4, "\n";
  s0, s1, s2, s3 := INil, INil, FullStreamAhead(2.4), EmptyList.INil;
  print s0, " ", s1, " ", s2, " ", s3, "\n";

  var n0: NonemptyList<bv7>;
  var n1: NonemptyCoList<bv7>;
  print n0, "\n";
  // print n1, "\n";
  n1 := CoAtom(109);
  print n1, "\n";

  var a: PinkColor;
  var b: Eight;
  var c: Odd;
  print a, " ", b, " ", c, "\n";
  
  var k0: real --> bool;
  var k1: real ~> bool;
  var k2: () --> int;
  var k3: (Color,set<bv12>) --> bv20;
  print k0, " ", k1, " ", k2, " ", k3, "\n";

  var m0: real -> bool;
  var m1: () -> int;
  var m2: (Color,set<bv12>) -> bv20;
  print m0, "\n";
  print m1, "\n";
  print m2, "\n";
}
