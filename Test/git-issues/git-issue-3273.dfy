// RUN: %exits-with 2 %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

iterator Iter<Y>(u: set<Y>) // this infers Y to be (==)

method Repro<K>() {
  var iter: Iter<K>; // error: K is not (==)
}

iterator IterA<X(==)>() // this declares X to be (==)

iterator IterB<Y>(u: set<Y>) // this infers Y to be (==)

method Test<K, L(==)>() {
  var a0: IterA<K>; // error: K is not (==)
  var a1: IterA<L>;
  var b0: IterB<K>; // error: K is not (==)
  var b1: IterB<L>;

  var c0: IterA?<K>; // error: K is not (==)
  var c1: IterA?<L>;
  var d0: IterB?<K>; // error: K is not (==)
  var d1: IterB?<L>;
}

iterator EqIter<Y>(u: set<Y>, x: Y, y: Y) yields (eq: bool)
  yield ensures eq == (x == y)
  ensures false
{
  while true {
    yield x == y;
  }
}

datatype Dt = Dt(a: int, ghost b: int)

method Main() {
  var d0 := Dt(0, 0);
  var d1 := Dt(0, 1);
  assert d0 != d1; // clearly

  // The following is error (but was not always detected by Dafny), because EqIter should take a (==) type argument.
  var iter: EqIter<Dt>; // error: Dt is not an equality-supporting type
  // The following does give an error, since the constructor lives in class EqIter whose
  // type parameer has been inferred to be (==).
  iter := new EqIter({}, d0, d1); // error: Dt is not an equality-supporting type
  var more := iter.MoveNext();
  assert more;
  assert iter.eq == (d0 == d1) == false; // according to the yield-ensures clause
  print iter.eq, "\n";
  if iter.eq {
    var ugh := 1 / 0; // according to the verifier, we never get here
  }
}
