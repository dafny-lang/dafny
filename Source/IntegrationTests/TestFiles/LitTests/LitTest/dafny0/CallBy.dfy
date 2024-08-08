// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s" -- --standard-libraries

datatype Option<+T> = None | Some(value: T) {
  function UnwrapOr(default: T): T {
    match this
    case Some(v) => v
    case None() => default
  }

  predicate IsFailure() {
    None?
  }

  function PropagateFailure<U>(): Option<U>
    requires None?
  {
    None
  }

  function Extract(): T
    requires Some?
  {
    value
  }
}

opaque predicate P() { true }

lemma ProveP() ensures P() {
  reveal P();
}

method M()
  requires P()
{}

method M'() returns (r: int)
  requires P()
  ensures r == 3
{ r := 3; }

method M''() returns (r: Option<int>)
  requires P()
{ r := None; }

method A() {
  M() by { ProveP(); }
  assert P(); // Should fail
}

method B() {
  var v: int;
  v := M'() by { reveal P(); }
  assert P(); // Should fail
}

method C() {
  assert p: P() by { ProveP(); }
  var v' := M'() by { reveal p; }
  assert v' == 3;  // should pass
  assert P(); // should fail
}

method D() returns (r: Option<int>){
  var v: int;
  v :- M''() by { ProveP(); }
  assert P(); // should fail
  r := None;
}

method E() returns (r: Option<int>){
  var v' :- M''() by { reveal P(); }
  assert P(); //  should fail
  r := None;
}
