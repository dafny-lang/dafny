// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

module {:options "/functionSyntax:4"} Stacks {
  export
    reveals Stack
    provides Stack.Valid, Stack.Repr, Stack.Elements
    reveals Stack.Count
    provides Stack.Push, Stack.Pop

  datatype MaybeInitialized<T> = ghost Uninitialized | Initialized(value: T)

  // Note, nothing is assumed about the type parameter T in the following line. In particular,
  // it's not assumed to be an auto-init type (and, in fact, may even be empty).
  class Stack<T> {
    ghost var Repr: set<object>
    ghost var Elements: seq<T>
    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      this in Repr &&
      arr in Repr &&
      n == |Elements| <= arr.Length != 0 &&
      forall i :: 0 <= i < n ==>
        arr[i].Initialized? && arr[i].value == Elements[i]
    }

    var arr: array<MaybeInitialized<T>>
    var n: nat

    constructor ()
      ensures Valid() && fresh(Repr) && Elements == []
    {
      Elements, n := [], 0;
      arr := new [20];
      Repr := {this, arr};
    }

    function Count(): nat
      requires Valid()
      reads Repr
    {
      |Elements|
    } by method {
      return n;
    }

    method Push(t: T)
      requires Valid()
      modifies Repr
      ensures Valid() && fresh(Repr - old(Repr))
      ensures Elements == old(Elements) + [t]
    {
      if n == arr.Length {
        var a := new [2 * n];
        forall i | 0 <= i < n {
          a[i] := arr[i];
        }
        arr := a;
        Repr := Repr + {a};
      }
      arr[n] := Initialized(t);
      Elements, n := Elements + [t], n + 1;
    }

    method Pop() returns (t: T)
      requires Valid() && Elements != []
      modifies Repr
      ensures Valid() && fresh(Repr - old(Repr))
      ensures var last := |old(Elements)| - 1;
        t == old(Elements)[last] &&
          Elements == old(Elements)[..last]
    {
      n := n - 1;
      Elements := Elements[..n];
      t := arr[n].value;
    }
  }
}

type Empty = x: int | false witness *

method Main() {
  var s := new Stacks.Stack();
  s.Push(10);
  s.Push(12);
  s.Push(11);
  var x := s.Pop();
  assert s.Elements == [10, 12] && x == 11;
  var count := s.Count();
  assert count == 2;
  print x, " ", count, "\n";

  var s' := new Stacks.Stack<Empty>();
  count := s'.Count();
  assert count == 0;
  print count, "\n";
}
