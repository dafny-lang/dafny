// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  ghost predicate Init(s: int) {
    s == 0
  }

  ghost predicate Next(s: int, s': int) {
    s' == s + 1
  }

  least predicate Reachable(s: int)
  {
    Init(s) || (exists s0 :: Reachable(s0) && Next(s0, s))
  }
}

module B {
  import A

  least lemma ReachableImpliesNonneg(s: int)
  requires A.Reachable(s)
  ensures s >= 0
  {
    if A.Init(s) {
    } else {
      var s0: int :| A.Reachable(s0) && A.Next(s0, s);
      ReachableImpliesNonneg(s0);
    }
  }
}

