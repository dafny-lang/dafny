// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s" -- --show-proof-obligation-expressions 

method GoodInstances(x: int, y: int) {
  assert (true decreases to false);
  assert (1 decreases to 0);
  assert (x decreases to x - 1);
  assert (x, y decreases to x, y - 1);
  var s := {x, y, x*y};
  var s' := s - {x};
  assert  (s, s, s decreases to s, s, s') ;
  assert (0 nonincreases to 0);
}

method Nested() {
  assert (true, (true decreases to false)) == (true, true);
}

method BadInstance1() {
  assert (0 decreases to 1);
}

method BadInstance2(x: int) {
  assert (x - 1 decreases to x);
}

method BadInstance3(x: int, y: int) {
  assert (x, y - 1 decreases to x, y);
}

// The following are failures in termination proofs, used to test the
// assertions printed with `--show-proof-obligation-expressions`

datatype List = Nil | Cons(head: int, tail: List)

function BadUp(m: nat, n: nat): List
  requires m <= n
  decreases n + m
{
  if m == n then Nil else Cons(m, BadUp(m+1, n))
}

method BadUpM(m: nat, n: nat) returns (r: List)
  requires m <= n
  decreases n + m
{
  if m == n {
    r := Nil;
  } else {
    var r' := BadUpM(m+1, n);
    r := Cons(m, r');
  }
}

method BadLoop(x: int, y: int) {
  var x' := x;
  var y' := x;
  while x' + y' > 0
    decreases x'
  {
    if x' > y' {
      x' := x' - 1;
    } else {
      y' := y' - 1;
    }
  }
}

method BadInstance4() {
  assert (0 nonincreases to 1);
}

method BadInstance5(i: int, b: bool) {
  assert (i decreases to b);
}

method BadInstance6() {
  assert (0 decreases to false);
}
