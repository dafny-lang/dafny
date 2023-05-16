// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

type MyInt = x | 6 <= x witness 6
newtype MyNewInt = x | 6 <= x witness 12

newtype short = x | -0x8000 <= x < 0x8000
newtype short' = x | -0x8000 <= x < 0x8000 witness -35

newtype FavoriateReals = r | r == 3.14 || r == 2.7 witness 3.14

type NonEmptyIntSet = s: set<int> | |s| != 0 witness {57}

type TypeSynonym<A,B> = (A, B)
type WithTypeParameters<A(==),B> = ignoreTypeParams: (int, bool) | true
  witness if var m: map<A,B> := map[]; |m| > 0 then (4, false) else (29, true)

datatype Dt = Atom(short') | More(Dt)

trait Tr {
  var u: MyNewInt
}

class MyClass extends Tr {
  var x: int
  var r: FavoriateReals
  var nes: NonEmptyIntSet
}

class MyClassWithCtor extends Tr {
  var x: int
  var r: FavoriateReals
  var nes: NonEmptyIntSet
  constructor Init(y: int)
  {
    new;
    nes := nes + {y};
  }
}

method Main()
{
  var m: MyInt;
  var n: MyNewInt;
  assert 6 <= m && 6 <= n;
  print "These are the arbitrary values chosen by the compiler: ", m, ", ", n, "\n";
  var s: short, s': short';
  print "short, short': ", s, ", ", s', "\n";
  var nes: NonEmptyIntSet;
  print "nes: "; PrintSet(nes); print "\n";
  var f0: TypeSynonym<int,bool>, f1: WithTypeParameters<int,bool>;
  print "f0, f1: ", f0, ", ", f1, "\n";
  var dt: Dt;
  print "dt: ", dt, "\n";
  var cl := new MyClass;
  print "cl { u: ", cl.u, ", x: ", cl.x, ", r: ", cl.r, ", nes: "; PrintSet(cl.nes); print " }\n";
  var cl' := new MyClassWithCtor.Init(20);
  print "cl' { u: ", cl'.u, ", x: ", cl'.x, ", ': ", cl'.r, ", nes: "; PrintSet(cl'.nes); print " }\n";
  AdvancedZeroInitialization.Test(0);
  AdvancedZeroInitialization.Test(1);
}

module AdvancedZeroInitialization {
  datatype Xt = MakeXt(x: int, s: seq<int>)
  datatype Yt<Y> = MakeYt(x: int, y: Y)
  type Even = x | x % 2 == 0

  // return the default value of an uninitialized local/out-parameter
  method MyMethod0<G(0)>(g: G) returns (h: G) {
  }
  // return the default value of an array element
  method MyMethod1<G(0)>(g: G) returns (h: G) {
    var a := new G[8];
    h := a[3];
  }

  method MyMethodSelect<G(0)>(which: int, g: G) returns (h: G)
    requires which == 0 || which == 1
  {
    if
    case which == 0 => h := MyMethod0(g);
    case which == 1 => h := MyMethod1(g);
  }

  method Test(which: int)
    requires which == 0 || which == 1
  {
    var x: real;
    var x' := MyMethodSelect(which, x);

    var ch: char;
    var ch' := MyMethodSelect(which, ch);

    var s: set<real>;
    var s' := MyMethodSelect(which, s);

    var d: Xt;
    var d' := MyMethodSelect(which, d);

    var y: Yt<seq<int>>;
    var y' := MyMethodSelect(which, y);

    var z: Yt<Even>;
    var z' := MyMethodSelect(which, z);

    print "\n";
    print "x: real :: ", x, " versus ", x', "\n";
    print "ch: char :: ", PrCh(ch), " versus ", PrCh(ch'), "\n";
    print "s: set :: ", s, " versus ", s', "\n";
    print "d: Xt :: ", d, " versus ", d', "\n";
    print "y: Yt<seq> :: ", y, " versus ", y', "\n";
    print "z: Yt<Even> :: ", z, " versus ", z', "\n";
  }
  // print '\0' in a way that git doesn't freak out about
  function PrCh(ch: char): string {
    if ch == '\0' then "'\\0'"
    else if ch == 'D' then "'D'"
    else "'(other char)'"
  }
}

// -------------------- set --------------------

method PrintSet(S: set<int>) {
  print "{";
  var s: set<int>, sep := S, "";
  while |s| != 0 {
    print sep;
    // pick smallest int in s
    ghost var m := ThereIsASmallest(s);
    var x :| x in s && forall y :: y in s ==> x <= y;
    print x;
    s, sep := s - {x}, ", ";
  }
  print "}";
}

lemma ThereIsASmallest(s: set<int>) returns (m: int)
  requires s != {}
  ensures m in s && forall y :: y in s ==> m <= y
{
  m :| m in s;
  if y :| y in s && y < m {
    var s' := s - {m};
    assert s == s' + {m};
    assert y in s';
    m := ThereIsASmallest(s');
  }
}
