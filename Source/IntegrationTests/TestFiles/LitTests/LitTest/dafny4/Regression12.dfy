// RUN: %exits-with 4 %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Some tests for the type inference that was revamped
// to better support subset types.

class VariousArrows {
  method Tests()
  {
    var c := InitArray(F);  // fine
    var d := InitArray(F');  // fine
    var e := InitArray(F'');  // fine
    if * {
      var f := InitArray(G);  // error: G is not a total function
    } else {
      var g := InitArray(G');  // error: G' is not a total function
    }
  }

  function F(x: int): char  // F has type int -> char
  { 'D' }

  function F'(x: int): char
    requires true  // the presence of a requires clause makes F' have type int --> char
  { 'D' }

  function F''(x: int): char
    reads {}  // the presence of a reads clause makes F' have type int ~> char
  { 'D' }

  function G(x: int): char
    requires x < 1900
  { 'D' }

  function G'(x: int): char
    reads this
  { 'D' }

  method InitArray<D>(f: int -> D) returns (a: D)
  {
    return f(44);
  }
}

// -----------------------

class Node { }

method Display(p: Node?) returns (s: set<Node>)
{
  var a := {p};
  var b := s - a;
  s := b;
}

method Display'(p: Node?) returns (s: set<Node>)
{
  s := s - {p};
}

method DisplayBad(p: Node?) returns (s: set<Node>)
{
  var a := {p};
  var b := s + a;
  s := b;  // error: cannot verify that "b" is a "set<Node>"
}

method DisplayCorrected(p: Node?) returns (s: set<Node>)
  requires p != null
{
  var a := {p};
  var b := s + a;
  s := b;
}

// -----------------------

class MyClass { }

method M(m: map<MyClass, MyClass>, s: set<MyClass>)
{
  assert null !in m;  // warning: null never in RHS
  assert null !in s;  // warning: null never in RHS
  assert null !in m.Keys;  // warning: null never in RHS
  assert null !in m.Values;  // warning: null never in RHS
}
