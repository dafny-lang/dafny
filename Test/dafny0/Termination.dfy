class Termination {
  method A(N: int)
    requires 0 <= N;
  {
    var i := 0;
    while (i < N)
      invariant i <= N;
      // this will be heuristically inferred:  decreases N - i;
    {
      i := i + 1;
    }
  }

  method B(N: int)
    requires 0 <= N;
  {
    var i := N;
    while (true)
      invariant 0 <= i;
      decreases i;
    {
      i := i - 1;
      if (!(0 <= i)) {
        break;
      }
    }
    assert i == -1;
  }

  method Lex() {
    call x := Update();
    call y := Update();
    while (!(x == 0 && y == 0))
      invariant 0 <= x && 0 <= y;
      decreases x, y;
    {
      if (0 < y) {
        y := y - 1;
      } else {
        x := x - 1;
        call y := Update();
      }
    }
  }

  method Update() returns (r: int)
    ensures 0 <= r;
  {
    r := 8;
  }

  method M() {
    var b := true;
    var i := 500;
    var r := new Termination;
    var s := {12, 200};
    var q := [5, 8, 13];
    while (true)
      decreases b, i, r;
//      invariant b ==> 0 <= i;
      decreases s, q;
    {
      if (12 in s) {
        s := s - {12};
      } else if (b) {
        b := !b;
        i := i + 1;
      } else if (20 <= i) {
        i := i - 20;
      } else if (r != null) {
        r := null;
      } else if (|q| != 0) {
        q := q[1..];
      } else {
        break;
      }
    }
  }

  method Q<T>(list: List<T>) {
    var l := list;
    while (l != #List.Nil)
      decreases l;
    {
      call x, l := Traverse(l);
    }
  }

  method Traverse<T>(a: List<T>) returns (val: T, b: List<T>);
    requires a != #List.Nil;
    ensures a == #List.Cons(val, b);
}

datatype List<T> {
  Nil;
  Cons(T, List<T>);
}

method FailureToProveTermination0(N: int)
{
  var n := N;
  while (n < 100) {  // error: may not terminate
    n := n - 1;
  }
}

method FailureToProveTermination1(x: int, y: int, N: int)
{
  var n := N;
  while (x < y && n < 100)  // error: cannot prove termination from the heuristically chosen termination metric
  {
    n := n + 1;
  }
}

method FailureToProveTermination2(x: int, y: int, N: int)
{
  var n := N;
  while (x < y && n < 100)  // error: cannot prove termination from the given (bad) termination metric
    decreases n - x;
  {
    n := n + 1;
  }
}

method FailureToProveTermination3(x: int, y: int, N: int)
{
  var n := N;
  while (x < y && n < 100)
    decreases 100 - n;
  {
    n := n + 1;
  }
}

method FailureToProveTermination4(x: int, y: int, N: int)
{
  var n := N;
  while (n < 100 && x < y)
    decreases 100 - n;
  {
    n := n + 1;
  }
}

method FailureToProveTermination5(b: bool, N: int)
{
  var n := N;
  while (b && n < 100)  // here, the heuristics are good enough to prove termination
  {
    n := n + 1;
  }
}

class Node {
  var next: Node;
  var footprint: set<Node>;

  function Valid(): bool
    reads this, footprint;
    // In a previous (and weaker) axiomatization of sets, there had been two problems
    // with trying to prove the termination of this function.  First, the default
    // decreases clause (derived from the reads clause) had been done incorrectly for
    // a list of expressions.  Second, the set axiomatization had not been strong enough.
  {
    this in footprint && !(null in footprint) &&
    (next != null  ==>  next in footprint &&
                        next.footprint < footprint &&
                        this !in next.footprint &&
                        next.Valid())
  }
}

method DecreasesYieldsAnInvariant(z: int) {
  var x := 100;
  var y := 1;
  var z := z;  // make parameter into a local variable
  while (x != y)
    // inferred: decreases |x - y|;
    invariant  (0 < x && 0 < y) || (x < 0 && y < 0);
  {
    if (z == 52) {
      break;
    } else if (x < y) {
      y := y - 1;
    } else {
      x := x - 1;
    }
    x := -x;
    y := -y;
    z := z + 1;
  }
  assert x - y < 100;  // follows from the fact that no loop iteration increases what's in the 'decreases' clause
}
