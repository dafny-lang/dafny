// RUN: %verify --referrers --type-system-refresh "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Test {
  var x: int
  const c: int
}

opaque function ReadFirstElement(a: array<int>)
  reads a`[0]  // Well-formedness error


opaque function ReadSecondElement(a: array<int>)
  requires a.Length >= 2
  reads a`[0]
{
  a[1]   // No rights no read this index
}

method ModifyArray(a: array<int>, c: bool)
  requires a.Length >= 2
  modifies a`[0]
{
  a[1] := 3; // Error, no rights to modify this index
}

method TestArray(a: array<int>, c: bool)
{
  ghost var m := a`[0]; // Error, could not prove a.Length >= 1
  ghost var m := a`[1]; // Error, could not prove a.Length >= 2
}

method TestArray2(a: array2<int>, c: bool)
{
  ghost var m := a`[0, 0]; // Error, could not prove a.Length1 and a.Length2 >= 1
}