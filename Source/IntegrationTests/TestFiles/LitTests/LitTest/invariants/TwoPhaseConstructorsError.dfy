// RUN: %exits-with 4 %verify --type-system-refresh --check-invariants "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class C {
  var valid: bool
  invariant valid

  constructor SinglePhase() {
    valid := true;
  }

  constructor TwoPhaseGood() {
    valid := true;
    new;
    valid := false;
    valid := true;
    foo(this); // no problem, invariant holds by this point
  }

  constructor TwoPhaseBad() {
    new;
    foo(this); // error
    valid := true;
  }

  static method foo(c: C) {
    assert c.valid by { assert c.invariant(); } // pass
  }
}