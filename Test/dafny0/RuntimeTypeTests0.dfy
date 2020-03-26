// RUN: %dafny /compile:3 "%s" /compileTarget:cs > "%t"
// RUN: %diff "%s.expect" "%t"

// The code in this file demonstrates complications in compiling to C# if a
// trait (like "object") is allowed as a type parameter to something compiled.
// The problem is that an assignment like a "seq<MyClass>" to a "seq<object>" requires
// covariance in the C# types they are compiled to, meaning a "Dafny.Sequence<S>" needs to be
// assignable to a "Dafny.Sequence<T>" if an S is assignable to a T.  Another example is an
// assignment of a "MyDatatype<MyClass>" to a "MyDatatype<object>".
//
// The solution is to ensure the Dafny type is mapped to a C# interface with the "out"
// type parameter modifier, which allows covariance under the condition that the type parameter
// is only used in return types in the interface methods and not as parameter types.
// This has only been implemented for sequences so far, but will apply to the other cases
// in this test case as well.
//
// A similar solution is possible (but not yet implemented) for Java, by using wildcard
// types: a "Dafny.Sequence<T>"" is assignable to a "Dafny.Sequence<? extends T>".
//
// Note that this is not a problem in JavaScript, which lacks type parameters.

method G()
{
  var s: set<int>;
  var t: set<nat>;
  // the following assignments are fine, because "s" and "t" are represented
  // the same way in C#
  s := {5, 7};
  t := s;
  s := t;
  print s, " and ", t, "\n";
}

trait Tr { var u: char }

class Class0 extends Tr { var x: int }

class Class1 extends Tr { var y: real }

datatype Dt<+A> = Atom(get: A)

method H() {
  var c := new Class0;
  var a: Dt<Class0> := Atom(c);
  var b: Dt<object>; // compilation error: compilation does not support trait types as a type parameter; consider introducing a ghost
  b := a;  
  print a, " and ", b, "\n";
}

method I()
{
  var c := new Class0;
  var a: Dt<Class0> := Atom(c);
  var b: Dt<object>; // compilation error: compilation does not support trait types as a type parameter; consider introducing a ghost
  b := a;
  print a, " and ", b, "\n";
}

method J()
{
  var c0 := new Class0;
  var c1 := new Class1;
  var s: set<Tr> := {c0, c1}; // compilation error: compilation of set<TRAIT> is not supported; consider introducing a ghost
  var t: set<Class0> := {c0};
  s := t;
  print s, " and ", t, "\n";
}

method K()
{
  var c0 := new Class0;
  var c1 := new Class1;
  var s: seq<Tr> := [c0, c1]; // no error, this is supported
  var t: seq<Class0> := [c0];
  s := t;
  print s, " and ", t, "\n";
}

method Main()
{
  G();
  H();
  I();
  J();
  K();
}
