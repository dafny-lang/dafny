// RUN: %exits-with 4 %verify --type-system-refresh --general-traits=datatype "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Empty = x: int | false witness *

class TestEmpty {
  const x: Empty

  constructor ()
    ensures false
  {
    x := 2; // error: RHS does not satisfy type constraint for Empty
    new;
  }
  constructor BadPrecondition(u: int)
    requires 10 / u == 2 // error: division by 0
    decreases *
  {
    for i := 0 to * {
    }
    new;
  }

  constructor BadPostcondition(u: int)
    // The following expression is fine, because the assumption generated between the well-formedness checks of the pre- and postconditions
    // should allow the verifier to derive false.
    ensures x as int is Empty && 10 / u == 2
    decreases *
  {
    for i := 0 to * {
    }
    new;
  }

  constructor Star() {
    x := *;
    new; // error: x is subject to definite assignment, but a ":= *" does not count for a possibly empty type
  }

}

// Repeat the class above, but with "var x" instead of "const x"
class TestEmptyWithVar {
  var x: Empty

  constructor ()
    ensures false
  {
    x := 2; // error: RHS does not satisfy type constraint for Empty
    new;
  }

  constructor BadPrecondition(u: int)
    requires 10 / u == 2 // error: division by 0
    decreases *
  {
    for i := 0 to * {
    }
    new;
  }

  constructor BadPostcondition(u: int)
    // The following expression is fine, because the assumption generated between the well-formedness checks of the pre- and postconditions
    // should allow the verifier to derive false.
    ensures x as int is Empty && 10 / u == 2
    decreases *
  {
    for i := 0 to * {
    }
    new;
  }

  constructor Star() {
    x := *;
    new; // error: x is subject to definite assignment, but a ":= *" does not count for a possibly empty type
  }
}

method CallEm()
  ensures false
{
  if
  case true =>
    var tc := new TestEmpty();
  case true =>
    var tv := new TestEmptyWithVar();
  case true =>
    var tc := new TestEmpty.Star();
    assert tc.x as int is Empty;
  case true =>
    var tv := new TestEmptyWithVar.Star();
    assert tv.x as int is Empty;
}

method Main() {
  CallEm();
  print 10 / 0, "\n";
}
