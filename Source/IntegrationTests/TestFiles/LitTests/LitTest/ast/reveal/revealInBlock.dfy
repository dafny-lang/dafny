// RUN: ! %verify --type-system-refresh --allow-axioms --isolate-assertions %s > %t
// RUN: %diff "%s.expect" "%t"

function P(x: int): bool {
  true
}

function Q(): int 
  requires P(0) {
  3
}

method IfScope() {
  hide *;
  if (*) {
    reveal P;
  } else {
    reveal P;
  }
  assert P(2); // error, since the previous two reveal statements are out of scope
}

method MatchStatementScope(x: int) {
  hide *;
  match x {
    case 0 =>
      reveal P;
      assert P(0);
    case _ =>
      assert P(0); // error
  }
  assert P(0); // no error because the previous assertions create an assume
  assert P(1); // error
}

method BlockScope() {
  hide *;
  {
    reveal P;
    assert P(0);
  }
  assert P(0); // no error because the previous assertion creates an assume
  assert P(1); // error
}

method Forall() {
  hide *;
  var aa := new int[3];
  forall i | 0 <= i < aa.Length
  {
    aa[i] := 0;
    // Somehow the next two lines cause the entire forall to become a ghost context
    // reveal P;
    // assert P(0);
  }
  assert P(1); // error
}

method While() {
  hide *;
  var x := 3;
  while(x > 0) {
    reveal P;
    assert P(0);
    x := x - 1;
  }
  assert P(1); // error
}

// If-alternative statement. Does anyone use that?
method IfAlternative(x: int) {
  hide *;
  if {
    case x == 0 => 
      reveal P;
      assert P(0);
    case x == 1 =>
      assert P(1); // error
    case true =>
  }
  assert P(2); // error
}

// Calc statement
method Calc() {
  hide *;
  calc {
    2;
    { reveal P; assert P(0); }
    1 + 1;
    { assert P(1); } // error
    1 + 1 + 0;
  }
  assert P(2); // error
}

// Check that we can still call a method hide
method hide() 
  decreases *
{
  hide();  
}

opaque function f(): int { 0 }

type T = x: int | true witness (reveal f(); 0)