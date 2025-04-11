// RUN: %tobinary %s > %t.assertFalse.dbin
// RUN: %verify --input-format Binary --stdin < %t.assertFalse.dbin > %t
// RUN: %diff "%s.expect" "%t"

datatype Pair = Pair(a: int, b: int)

datatype Flag = Ok | Err(err: int) {
  function IsFailure(): bool {
    this.Err?
  }

  function PropagateFailure(): int requires IsFailure() {
    this.err
  }
}

datatype Extractable = Good(good: int) | Bad(bad: int) {
  function IsFailure(): bool {
    this.Bad?
  }

  function PropagateFailure(): int requires IsFailure() {
    this.bad
  }

  function Extract(): int
    requires !IsFailure()
  {
    this.good
  }
}

method LetExpressions() {
  var l0 := {
    var x := 1; x * 2
  };
  var l1 := {
    var (x, y) := (2, 3); x + y
  };
  var l2 := {
    var x, y := 4, 5; x + y
  };
  var l3 := {
    var Pair(x, y) := Pair(6, 7); x + y
  };
}

method LetOrFailExpressions() returns (out: int) {
  var f0 := {
    var x :- Bad(0); x
  };
  var y := (:- Err(1); 2);
  return y + 3;
}