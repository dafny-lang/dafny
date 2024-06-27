// RUN: %exits-with 4 %verify --show-proof-obligation-expressions "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class C {
  var x: int
  var y: int
  method ModifyClassField()
    modifies this`y
  {
    x := 0;
  }
}

class C2 {
  var x: int
  var y: int
}

method ModifyObject(s: seq<C>, t: seq<C2>)
  requires |s| > 1
  requires |t| > 0
  // singletons
  modifies s[1]           // no field
  modifies (s[1] as C)`x  // right field
  modifies (s[0] as C)`y  // right object, wrong field
  modifies (t[0] as C2)`x // wrong type, right field name
  // sets
  modifies {s[1]}         // no field
  modifies {s[1] as C}`x  // right field
  modifies {s[0] as C}`y  // right object, wrong field
  modifies {t[0] as C2}`x // wrong type, right field name
{
  s[0].x := 1;
}

method ModifyObjects(s: seq<C>)
  requires |s| > 1
  modifies s[1]
  modifies (set c | c in s)`y
{
  forall c | c in s {
    c.x := 1;
  }
}

method ModifyArray(a: array<int>, b: array<int>)
  modifies b
{
  if a.Length > 0 {
    a[0] := 1;
  }
}

method ModifyArrays(s: seq<array<int>>)
  requires |s| > 1
  modifies s[1]
{
  forall a | a in s && a.Length > 0 {
    a[0] := 1;
  }
}

method ModifyMultiDimArray(a: array2<int>)
{
  if a.Length0 > 0 && a.Length1 > 0 {
    a[0, 0] := 1;
  }
}