// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


ghost function RangeMask(from: nat, to: nat): bv6

lemma CalcEqBits(i: nat, j: nat)
{
  // regression: the following once caused a crash in type inference (missing cases for bitvectors)
  calc == {
    RangeMask(i, j);
    -1 << (6 - j); // error (x2): invalid shift amount, and calc step doesn't hold
  }
}
