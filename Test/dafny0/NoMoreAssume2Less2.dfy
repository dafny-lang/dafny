// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method M0(n: nat) {
  var i := 0;
  while i < n {
    i := i + 1;
  }
  assert n == 0; // error
}

method M1(n: nat) {
  var i := 0;
  while i < n {
    assume false;
    i := i + 1;
  }
  assert n == 0; // error
}

method M2(n: nat) {
  var i := 0;
  while i < n {
    assume 2 < 2;
    i := i + 1;
  }
  assert n == 0; // error
}

method M3(n: nat) {
  var i := 0;
  while i < n {
    assert false; // error
    i := i + 1;
  }
  assert n == 0; // error
}

method M4(n: nat) {
  var i := 0;
  while i < n {
    assert 2 < 2; // error
    i := i + 1;
  }
  assert n == 0; // error
}

method M5(n: nat) {
  var i := 0;
  while i < n {
    assert false by { // error
    }
    i := i + 1;
  }
  assert n == 0; // error
}

predicate P() { true }
predicate Q() { true }
predicate R(n: nat) { true }
predicate False() { false }

method Conjuncts0(n: nat) {
  var i := 0;
  while i < n {
    assume P() && false && Q();
    i := i + 1;
  }
  assert n == 0; // error
}

method Conjuncts1(n: nat) {
  var i := 0;
  while i < n {
    assert P() && false && Q(); // error
    i := i + 1;
  }
  assert n == 0; // error
}

method Conjuncts2(n: nat) {
  var i := 0;
  while i < n {
    assume False();
    i := i + 1;
  }
  assert n == 0; // error
}

method Conjuncts3(n: nat) {
  var i := 0;
  while i < n {
    assert False(); // error
    i := i + 1;
  }
  assert n == 0; // error
}

method Conjuncts4(n: nat, m: nat) {
  var i := 0;
  while i < n {
    assert R(m) && false; // error
    i := i + 1;
  }
  assert n == 0; // error
}

method LoopInvariants(n: nat) {
  var i := 0;
  while i < n {
    for j := 0 to 5
      invariant false // error
    {
    }
    i := i + 1;
  }
  assert n == 0; // error
}

method Calls0(n: nat) {
  var i := 0;
  while i < n {
    FalsePre(); // error
    i := i + 1;
  }
  assert n == 0; // error
}

method Calls1(n: nat) {
  var i := 0;
  while i < n {
    FalsePost();
    i := i + 1;
  }
  assert n == 0; // error
}

method FalsePre()
  requires false

method FalsePost()
  ensures false

method LabeledExpressions0(n: nat)
  requires A: false
{
  var i := 0;
  while i < n {
    reveal A;
    i := i + 1;
  }
  assert n == 0; // error
}

method LabeledExpressions1(n: nat)
{
  assert A: false; // error
  var i := 0;
  while i < n {
    reveal A;
    i := i + 1;
  }
  assert n == 0; // error
}

method LabeledExpressions2(n: nat)
{
  assert A: false by { // error
  }
  var i := 0;
  while i < n {
    reveal A;
    i := i + 1;
  }
  assert n == 0; // error
}
