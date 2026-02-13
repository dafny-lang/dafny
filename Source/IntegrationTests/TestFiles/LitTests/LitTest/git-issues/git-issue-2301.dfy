// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


class Twostate {
  var z: int

  twostate predicate NoChange_ReadsThis()
    reads this
  {
    unchanged(this)
  }

  twostate predicate NoChange_ReadsNothing()
  {
    unchanged(this) // error: insufficient reads clause
  }

  method Test0()
    modifies this
  {
    assert NoChange_ReadsThis();
    z := z + 1;
    assert NoChange_ReadsThis(); // error: does not hold
  }

  method Test1()
    modifies this
  {
    assert NoChange_ReadsNothing();
    z := z + 1;
    // If NoChange_ReadsNothing has an empty reads clause, then the following assertion
    // from the previous assertion.
    assert NoChange_ReadsNothing();
  }

  twostate predicate BadVariations0(c: Twostate, d: Twostate, e: Twostate, f: Twostate)
  {
    unchanged(
      this, // error: insufficient reads clause
      c // error: insufficient reads clause
    )
  }

  twostate predicate BadVariations1(c: Twostate, d: Twostate, e: Twostate, f: Twostate)
  {
    unchanged({c, d}) // error: insufficient reads clause
  }

  twostate predicate BadVariations2(c: Twostate, d: Twostate, e: Twostate, f: Twostate)
  {
    unchanged(
      multiset{e, e, c, e}, // error: insufficient reads clause
      [c, d, e], // error: insufficient reads clause
      [c, f, e, d] // error: insufficient reads clause
    )
  }

  twostate predicate GoodVariations(c: Twostate, d: Twostate, e: Twostate, f: Twostate)
    reads this, c, {d, e}, multiset{f}
  {
    && unchanged(this, c)
    && unchanged({c, d})
    && unchanged(multiset{e, e, c, e}, [c, d, e], [c, f, e, d])
  }
}
