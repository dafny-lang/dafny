// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The code in this file demonstrates complications in compiling to C# if a
// trait (like "object") is allowed as a type parameter to something compiled.
// The problem is that assignment like a "set<MyClass>" to a "set<object>", which
// is allowed in Dafny, would require a deep copy in C#.  Another example is an
// assignment of a "MyDatatype<MyClass>" to a "MyDatatype<object>".
// Currently, the Dafny compiler enforces restrictions that rule out the expensive
// cases.  A possibly more friendly approach would be to emit code that performs
// the deep copies.

method G()
{
  var s: set<int>;
  var t: set<nat>;
  // the following assignments are fine, because "s" and "t" are represented
  // the same way in C#
  s := {5, 7};
  t := s;
  s := t;
}

trait Tr { var u: char }

class Class0 extends Tr { var x: int }

class Class1 extends Tr { var y: real }

datatype Dt<+A> = Atom(get: A)

method H() {
  var c := new Class0;
  var a: Dt<Class0> := Atom(c);
  var b: Dt<object>;
  b := a;  // compilation error: this would be hard to compile to C#
}

method I()
{
  var c := new Class0;
  var a: Dt<Class0> := Atom(c);
  var b: Dt<object>;
  b := a;  // compilation error: this would be hard to compile to C#
}

method J()
{
  var c0 := new Class0;
  var c1 := new Class1;
  var s: set<Tr> := {c0, c1};
  var t: set<Class0> := {c0};
  s := t;  // compilation error: this would be hard to compile to C#
}

method Main()
{
  G();
  H();
  I();
  J();
}
