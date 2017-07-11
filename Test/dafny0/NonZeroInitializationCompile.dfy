// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type MyInt = x | 6 <= x witness 6
newtype MyNewInt = x | 6 <= x witness 12

newtype short = x | -0x8000 <= x < 0x8000
newtype short' = x | -0x8000 <= x < 0x8000 witness -35

newtype FavoriateReals = r | r == 3.14 || r == 2.7 witness 3.14

type NonEmptyIntSet = s: set<int> | |s| != 0 witness {57}

type TypeSynonym<A,B> = (A, B)
type WithTypeParameters<A,B> = ignoreTypeParams: (int, bool) | true
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
  print "nes: ", nes, "\n";
  var f0: TypeSynonym<int,bool>, f1: WithTypeParameters<int,bool>;
  print "f0, f1: ", f0, ", ", f1, "\n";
  var dt: Dt;
  print "dt: ", dt, "\n";
  var cl := new MyClass;
  print "cl { u: ", cl.u, ", x: ", cl.x, ", r: ", cl.r, ", nes: ", cl.nes, " }\n";
  var cl' := new MyClassWithCtor.Init(20);
  print "cl' { u: ", cl'.u, ", x: ", cl'.x, ", ': ", cl'.r, ", nes: ", cl'.nes, " }\n";
}
