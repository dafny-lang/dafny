// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type IntSeq = seq<int>
method Test0()
{
  var a;
  var b := [a];
  var s: IntSeq := a;
}

type BoolSet = set<bool>
method Test1()
{
  var a;
  var b := {a};
  var s: BoolSet := a;
}

method RepeatAux()
{
  var a;
  var b := [a];
  var s: string := a;
}

method RepeatAux2<A>()
{
  var s;
  var s': string := s;
  var s'' := s + s;
}

datatype Option<X> = None | Some(X)
type OptionReal = Option<real>
method Test2()
{
  var a;
  var b := Some(a);
  var s: OptionReal := a;
}
