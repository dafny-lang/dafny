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

const TWO := 2

method MatchStmt(i: int, b: bool) {
  match i {
    case 1 => print "1";
    case TWO => print "2";
    case 3 | 4 => print "3 or 4";
    case other => {
      match (other, b) {
        case (-1, b') => print "negative";
        case (i', true) => print "true";
        case tuple => print "other tuple";
      }
    }
  }
  match Pair(i + 1, i * 2) {
    case Pair(5, y) => print "Pair(5, ?)";
    case Pair(x, 6) => print "Pair(?, 6)";
    case pair => print "other pair";
  }
}

method MatchExpr(i: int, b: bool) {
  var s1 := match i {
    case 1 => "1"
    case TWO => "2"
    case 3 | 4 => "3 or 4"
    case other => 
      match (other, b) {
        case (-1, b') => "negative"
        case (i', true) => "true"
        case tup => "other"
      }
  };
  var s2 := match Pair(i + 1, i * 2) {
    case Pair(5, y) => "Pair(5, ?)"
    case Pair(x, 6) => "Pair(?, 6)"
    case pair => "other pair"
  };
  print s1, s2;
}
