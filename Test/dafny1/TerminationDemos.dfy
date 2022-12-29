// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Example {
  method M(n: int)
  {
    var i := 0;
    while i < n
    {
      i := i + 1;
    }
  }
}

// -----------------------------------

class Fibonacci {
  function Fib(n: int): int
  {
    if n < 2 then n else Fib(n-2) + Fib(n-1)
  }
}

// -----------------------------------

class Ackermann {
  function F(m: int, n: int): int
  {
    if m <= 0 then
      n + 1
    else if n <= 0 then
      F(m - 1, 1)
    else
      F(m - 1, F(m, n - 1))
  }

  function G(m: int, n: int): int
    requires 0 <= m && 0 <= n
    ensures 0 <= G(m, n)
  {
    if m == 0 then
      n + 1
    else if n == 0 then
      G(m - 1, 1)
    else
      G(m - 1, G(m, n - 1))
  }

  function H(m: nat, n: nat): nat
  {
    if m == 0 then
      n + 1
    else if n == 0 then
      H(m - 1, 1)
    else
      H(m - 1, H(m, n - 1))
  }

  method ComputeAck(m: nat, n: nat) returns (r: nat)
  {
    if m == 0 {
      r := n + 1;
    } else if n == 0 {
      r := ComputeAck(m - 1, 1);
    } else {
      var s := ComputeAck(m, n - 1);
      r := ComputeAck(m - 1, s);
    }
  }
}

// -----------------------------------

class List {
  var data: int
  var next: List?
  ghost var ListNodes: set<List>
  predicate IsAcyclic()
    reads *
    decreases ListNodes
  {
    this in ListNodes &&
    (next != null ==>
      next.ListNodes <= ListNodes && this !in next.ListNodes &&
      next.IsAcyclic())
  }

  method Singleton(x: int) returns (list: List)
    ensures list.IsAcyclic()
  {
    list := new List;
    list.data := x;
    list.next := null;
    list.ListNodes := {list};
  }

  method Prepend(x: int, tail: List?) returns (list: List)
    requires tail == null || tail.IsAcyclic();
    ensures list.IsAcyclic();
  {
    list := new List;
    list.data := x;
    list.next := tail;
    list.ListNodes := if tail == null then {list} else {list} + tail.ListNodes;
  }

  function Sum(): int
    requires IsAcyclic()
    reads *
    decreases ListNodes
  {
    if next == null then data else data + next.Sum()
  }
}
