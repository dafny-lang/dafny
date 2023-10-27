// RUN: %verify --warn-contradictory-assumptions "%s" > "%t"
// Check that the output contains no warnings about contradictory assumptions
// RUN: %diff "%s.expect" "%t"

abstract module PR4715Test {
  opaque function Pow(b: int, e: nat): int
    decreases e
  {
    if e == 0 then
      1
    else
      b * Pow(b, e - 1)
  }

  function WeirdIdentity(x: int): (r: int)
    ensures r == x
  {
    if x < 0 then
      assert Pow(1, 2) == 1 by { reveal Pow(); }
      x
    else
      x
  }

}

module PR4715Test2 refines PR4715Test {
}
