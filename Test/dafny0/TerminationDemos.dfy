class Example {
  method M(n: int)
  {
    var i := 0;
    while (i < n)
      decreases n - i;
    {
      i := i + 1;
    }
  }
}

// -----------------------------------

class Fibonacci {
  function Fib(n: int): int
    decreases n;
  {
    if n < 2 then n else Fib(n-2) + Fib(n-1)
  }
}

// -----------------------------------

class Ackermann {
  function F(m: int, n: int): int
    decreases m, n;
  {
    if m <= 0 then
      n + 1
    else if n <= 0 then
      F(m - 1, 1)
    else
      F(m - 1, F(m, n - 1))
  }
}

// -----------------------------------

class List {
  var data: int;
  var next: List;
  ghost var ListNodes: set<List>;
  function IsAcyclic(): bool
    reads *;
    decreases ListNodes;
  {
    this in ListNodes &&
    (next != null ==>
      next.ListNodes <= ListNodes && this !in next.ListNodes &&
      next.IsAcyclic())
  }

  method Singleton(x: int) returns (list: List)
    ensures list != null && list.IsAcyclic();
  {
    list := new List;
    list.data := x;
    list.next := null;
    list.ListNodes := {list};
  }

  method Prepend(x: int, tail: List) returns (list: List)
    requires tail == null || tail.IsAcyclic();
    ensures list != null && list.IsAcyclic();
  {
    list := new List;
    list.data := x;
    list.next := tail;
    list.ListNodes := if tail == null then {list} else {list} + tail.ListNodes;
  }

  function Sum(): int
    requires IsAcyclic();
    reads *;
    decreases ListNodes;
  {
    if next == null then data else data + next.Sum()
  }
}
