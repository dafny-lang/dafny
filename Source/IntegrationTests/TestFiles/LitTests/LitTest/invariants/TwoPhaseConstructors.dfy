// RUN: %exits-with 4 %verify --type-system-refresh --check-invariants "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class C {
  var valid: bool
  invariant valid

  constructor SinglePhaseGood() {
    valid := true; // ok
  }
  
  constructor SinglePhaseError() {
    valid := false; // error
  }

  constructor TwoPhaseGood() {
    valid := true;
    valid := false;
    valid := true;
    new;
    valid := true;
    foo(this); // no problem, invariant holds by this point
  }

  constructor TwoPhaseBad() {
    new; // error: invariant doesn't hold by new;
    valid := true;
    foo(this);
  }

  static method foo(c: C) {
    assert c.valid; // pass
  }
}