// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
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

method Test4(x: Trait, m: array2<Class>)
  requires m.Length0 > 0 && m.Length1 > 0
  modifies m
{
  m[0, 0] := x;   // Error: should fail in verifier, not resolver
}

method Test5(x: Trait?)
{
  var m: array2 := new Class?[10, 10];
  m[0, 0] := x;   // Error: should fail in verifier, not resolver
}

method Test6()
{
  var t: Trait := new Class;
  var c: Class := t; // OK
}

class ClassB extends Trait { }

method Test7()
{
  var t: Trait := new ClassB;
  var c: Class := t; // error in verifier
}

method Test8(cn: Class?) {
  var c: Class := cn;
}

class ClassT<T> extends Trait {}

method Test9(cc: ClassT?) {
  var c: ClassT := cc;
}
