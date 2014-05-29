// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Array<T>
{
   var Length: nat;
}

class Test<T> {
  var a: Array<int>;
  var b: Array<T>;
  predicate valid()
      reads this, a, b;
  {
      a != null && b != null && a != b && a.Length == b.Length
  }
}

method m1<T, U>(t: T, u: U)
   requires t != u; // Cannot compare type parameters (can only compare reference types that could be the same)
{
   
}

method m2<T>(t: array<T>, a: array<int>)
   requires t != null && a != null && t != a && t.Length == a.Length;
{

}


class Weird<T, U, V>
{

}


method m3<T, V>(a: Weird<T, int, V>, b: Weird<T, bool, V>)
   requires a == b; // Bad: second parameter can't be both bool and int.
{

}


method m4<T, U, V>(a: Weird<T, U, V>, b: Weird<T, bool, V>)
  requires a == b;
{

}


// Just to make sure nothing went wrong.
method m5(a: array<int>, b: array<bool>)
   requires a == b; // Bad: never equal
{

}
