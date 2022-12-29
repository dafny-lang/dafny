// RUN: %baredafny run %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method M1()
{
  var m := map [{10, 20} := 33];
  assert {10, 20} in m; // succeeds
  print {10, 20} in m, "\n"; // prints False
}

method M1'()
{
  var m := map [{10, 20} := 33];
  assert {10, 20} == {20, 10};
  assert {20, 10} in m; // succeeds
  print {20, 10} in m, "\n"; // prints False
}

method M2()
{
  var m := map [(map [1 := 10, 2 := 20]) := 33];
  assert (map [1 := 10, 2 := 20]) in m; // succeeds
  print (map [1 := 10, 2 := 20]) in m, "\n"; // prints False
}

method M2'()
{
  var m := map [(map [1 := 10, 2 := 20]) := 33];
  assert (map [1 := 10, 2 := 20] == map [2 := 20, 1 := 10]);
  assert (map [2 := 20, 1 := 10]) in m; // succeeds
  print (map [2 := 20, 1 := 10]) in m, "\n"; // prints False
}

method M3()
{
  var m := map [(multiset{10, 20}) := 33];
  assert (multiset{10, 20}) in m; // succeeds
  print (multiset{10, 20}) in m, "\n"; // prints False
}

method M3'()
{
  var m := map [(multiset{10, 20}) := 33];
  assert multiset{10, 20} == multiset{20, 10};
  assert (multiset{20, 10}) in m; // succeeds
  print (multiset{20, 10}) in m, "\n"; // prints False
}

method M4()
{
  var m := map [[10, 20] := 33];
  assert [10, 20] in m; // succeeds
  print [10, 20] in m, "\n"; // prints False
}

method Main()
{
  M1();
  M1'();
  M2();
  M2'();
  M3();
  M3'();
  M4();
}
