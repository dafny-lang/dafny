// RUN: %exits-with 2 %dafny /dprint:- /env:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
module Tests {
  predicate P(n: int)

  predicate R(r: real)

  method M0()
  {
    if x :| P(x) {
      var y := x + 3;
      var x := true;  // error: 'x' is already declared in this scope
    }
  }

  method M1()
  {
    if x: int :| P(x) {
      x := x + 1;  // error: 'x' is an immutable variable
    }
  }

  method M2()
  {
    var x := true;
    if x, y :| P(x) && R(y) {  // this declares a new 'x'
      var z := x + 12;
    }
    x := x && false;
  }

  method M3()
  {
    var x := true;
    if x: int, y :| P(x) && R(y) {
      var z := x + y as int;
      var w := x as real + y;
    }
    var x := 0.0;  // error: 'x' is already declared in this scope
  }

  method M4()
  {
    if x, y: real :| P(x) && R(y) {
    }
  }

  method M5()
  {
    if x: int, y: real :| P(x) && R(y) {
    }
  }

  method M6()
  {
    if x {:myattribute x, "hello"} :| P(x) {
    }
    if x, y {:myattribute y, "sveika"} :| P(x) && R(y) {
    }
    if x: int {:myattribute x, "chello"} :| P(x) {
    }
    if x {:myattribute x, "hola"} {:yourattribute x + x, "hej"} :| P(x) {
    }
  }

  method M7()
  {
    if x :| P(x) {
    } else if * {
    } else if y :| R(y) {
    } else if y :| P(y) {
    }
  }

  method P0(m: int, n: int)
    requires m < n
  {
    var x := true;
    if {
      case x :| P(x) =>
        var t := 3 * x;
      case x: int :| P(x) =>
      case x, y :| P(x) && R(y) =>
        y := y + 1.0;  // error: 'y' is an immutable variable
      case x: int, y :| P(x) && R(y) =>
      case m < n =>
        x := x || m + 5 == n;
      case x, y: real :| P(x) && R(y) =>
      case x: int, y: real :| P(x) && R(y) =>
    }
    assert x;
  }

  method P1(m: int, n: int)
    requires m < n
  {
    if {
      case x {:myattribute x, "hello"} :| P(x) =>
      case x, y {:myattribute y, "sveika"} :| P(x) && R(y) =>
      case x: int {:myattribute x, "chello"} :| P(x) =>
      case x {:myattribute x, "hola"} {:yourattribute x + x, "hej"} :| P(x) =>
      case m < n =>
    }
  }
}
module TypesNotFullyDetermined {
  method T0()
  {
    if x :| true {  // error: type not entirely resolved
    }
  }
  method T1()
  {
    if x :| true {
      var y := x + 3;
    }
  }
}

module Ghost {
  predicate P(x: int)  // note, P is ghost
  predicate method R(x: int)
  method M7() returns (z: int, b: bool)
  {
    if * {
      z := z + -z;
    } else if y :| 1000 <= y < 2000 && R(y) {
      z := y;
    } else if y :| 0 <= y < 100 && P(y) {
      z := y;  // error: not allowed, because the P in the guard makes this a ghost context
    } else if y :| 0 <= y < 100 && R(y) {
      z := y;  // error: this is also in a ghost context, because it depends on the P above
    }

    if * {
      z := z + -z;
    } else if exists y :: 1000 <= y < 2000 && R(y) {
      z := 0;
    } else if exists y :: 0 <= y < 100 && P(y) {
      z := 0;  // error: not allowed, because the P in the guard makes this a ghost context
    } else if exists y :: 0 <= y < 100 && R(y) {
      z := 0;  // error: this is also in a ghost context, because it depends on the P above
    }

    if P(z) {
      z := 20;  // error: blatant ghost context
    }

    b := exists y :: 0 <= y < 100 && P(y);  // error: assignment to non-ghost of something that depends on ghost
    ghost var c;
    c := exists y :: 0 <= y < 100 && P(y);
    b := exists y {:myattribute P(y)} :: 0 <= y < 100;
  }
}
