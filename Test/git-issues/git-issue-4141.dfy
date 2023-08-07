// RUN: %testDafnyForEachCompiler "%s"

method Main()
{
  var a := new bool[1];
  var ars := [a];
  a := new bool[1];
  var ars' := [a];
  print ars == ars', "\n";
  ars[0][0] := true;
  print ars == ars', "\n";
  ars'[0][0] := true;
  print ars == ars', "\n";
  print [ars[0]] == [ars[0]], "\n";
}