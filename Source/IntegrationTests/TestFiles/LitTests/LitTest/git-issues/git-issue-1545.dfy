// RUN: %testDafnyForEachResolver --expect-exit-code=2 --refresh-exit-code=4 "%s"

ghost predicate Foo(s: seq<int>) {
  // Under the legacy resolver, a type test for a subset type is not allowed
  forall i :: 0 <= i < |s| ==> i is nat // error (legacy resolver)
}

type Not3 = x: int | x != 3

lemma Tests(s: seq<int>) {
  if
  case true =>
    assert forall i :: 0 <= i < |s| ==> i is int;
  case true =>
    assert forall i :: 0 <= i < |s| ==> i is nat; // error (legacy resolver)
  case true =>
    assert forall i :: -2 <= i < |s| ==> i is nat; // error (legacy resolver, and verification with resolver refresh)
  case true =>
    assert forall i :: 0 <= i < |s| ==> i is Not3; // error (legacy resolver, and verification with resolver refresh)
  case true =>
    assert forall i :: 4 <= i < |s| ==> i is Not3; // error (legacy resolver)
}

lemma MoreTests(s: seq<int>) {
  if
  case true =>
    assert forall i: nat :: 0 <= i < |s| ==> i is int;
  case true =>
    assert forall i: nat :: 0 <= i < |s| ==> i is nat;
  case true =>
    assert forall i: nat :: -2 <= i < |s| ==> i is nat;
  case true =>
    assert forall i: Not3 :: 0 <= i < |s| ==> i is Not3;
  case true =>
    assert forall i: nat :: 4 <= i < |s| ==> i is Not3; // error (legacy resolver)
}

type Not5Either = x: Not3 | x != 5
type Not3Or5 = x: int | x != 3 && x != 5

lemma EvenMoreTests(s: seq<int>) {
  if
  case true =>
    assert forall i: int :: 7 <= i < |s| ==> i is nat; // error (legacy resolver)
  case true =>
    assert forall i: Not3 :: 7 <= i < |s| ==> i is nat; // error (legacy resolver)
  case true =>
    assert forall i: Not5Either :: 7 <= i < |s| ==> i is Not3;
  case true =>
    assert forall i: Not3Or5 :: 7 <= i < |s| ==> i is Not3; // error (legacy resolver)
}

lemma FinalTests(s: seq<int>) {
  if
  case true =>
    assert forall i: Not3Or5 :: -2 <= i < |s| ==> i is Not5Either; // error (legacy resolver)
  case true =>
    assert forall i: Not5Either :: -2 <= i < |s| ==> i is Not3Or5; // error (legacy resolver)
  case true =>
    assert forall i: Not3 :: -2 <= i < |s| ==> i is Not5Either; // error (legacy resolver, and verification with resolver refresh)
  case true =>
    assert forall i: Not3Or5 :: -2 <= i < |s| ==> i is Not5Either; // error (legacy resolver)
}
