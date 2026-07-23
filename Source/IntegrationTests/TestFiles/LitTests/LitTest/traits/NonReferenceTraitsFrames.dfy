// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s" -- --general-traits=datatype --general-newtypes=false

// Regression test for https://github.com/dafny-lang/dafny/issues/6470.
// Under --general-traits=datatype (the default for Dafny 5.0), a bare trait
// is not a reference type. Reads/modifies/unchanged/fresh on a non-reference
// trait should produce a tailored error message suggesting `extends object`,
// not the generic one that points to `--referrers`.

module Tests {
  class Bank { }

  trait Account {
    var bank: Bank
  }

  // reads clause, directly on a trait value
  function GetBank(a: Account): Bank
    reads a // error: non-reference trait
  { a.bank }

  // reads clause, on a field location of a trait value
  function GetBank2(a: Account): Bank
    reads a`bank // error: non-reference trait
  { a.bank }

  // reads clause, on a set of trait values
  function GetSize(accts: set<Account>): int
    reads accts // error: non-reference trait
  { 0 }

  // modifies clause
  method SetBank(a: Account, b: Bank)
    modifies a // error: non-reference trait
  { a.bank := b; }

  // unchanged expression
  twostate predicate SameBank(a: Account)
  { unchanged(a) } // error: non-reference trait

  // fresh expression
  twostate predicate IsFresh(a: Account)
  { fresh(a) } // error: non-reference trait

  // fresh on a set of traits
  twostate predicate AllFresh(s: set<Account>)
  { fresh(s) } // error: non-reference trait
}

// Positive control: with `extends object`, the same shapes verify cleanly.
module TestsOk {
  class Bank { }

  trait Account extends object {
    var bank: Bank
  }

  function GetBank(a: Account): Bank
    reads a
  { a.bank }

  method SetBank(a: Account, b: Bank)
    modifies a
  { a.bank := b; }
}
