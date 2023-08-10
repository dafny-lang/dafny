// RUN: %testDafnyForEachCompiler "%s"

method Test<X(==)>(a: X, b: X) {
    print a == b, "\n";
}

method Main()
{
  var a := new bool[1];
  var ars := [a];
  a := new bool[1];
  var ars' := [a];
  Test(ars, ars');
  ars[0][0] := true;
  Test(ars, ars');
  ars'[0][0] := true;
  Test(ars, ars');
  Test([ars[0]], [ars[0]]);
}
