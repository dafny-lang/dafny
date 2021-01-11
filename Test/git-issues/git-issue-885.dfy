// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait Trait { }
class Class extends Trait { }

method Test1(x: Trait)
{
  var a := new Class?[1];
  a[0] := x;      // Error: should fail in verifier, not resolver
}

method Test2(x: Trait)
{
  var c: Class;
  c := x;         // Error: should fail in verifier, not resolver
}

method Test3(x: Trait?)
{
  var m: array2<Class?> := new Class?[10, 10];
  m[0, 0] := x;   // Error: should fail in verifier, not resolver
}

method Test4(x: Trait)
{
  var m: array2<Class> := new Class[10, 10];
  m[0, 0] := x;   // Error: should fail in verifier, not resolver
}

