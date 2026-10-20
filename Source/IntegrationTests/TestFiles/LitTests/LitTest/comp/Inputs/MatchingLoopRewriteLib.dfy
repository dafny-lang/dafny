module Library {
  // Not split, so that the trigger generator's triggers, with the term i + 1 that it names for them, are on the
  // quantifier itself
  predicate Sorted(s: seq<int>) {
    forall i {:split false} :: 0 <= i < |s| - 1 ==> s[i] <= s[i + 1]
  }
}
