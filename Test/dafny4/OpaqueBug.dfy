// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate inner(x:int, y:int) { x == y}

predicate {:opaque} secret(w:int, z:int) { inner(w, z) }

method test(m:int, n:int)
    // A previous bug in SplitExpr meant that this mention of secret
    // caused its body to be inlined, bypassing opaque
    requires secret(m, n);
{
    assert m == n;      // error: secret is opaque
}

// A previous implementation of opaque allowed the Lit axioms to bypass
// an opaque annotation.  This affect both function calls with Lit arguments,
// and functions that take no arguments
function A(): int { 6 }
function {:opaque} B(): int { A() }
lemma AB()
{
  assert B() == 6;  // error: B is opaque
}

