// RUN: %exits-with 4 %dafny "%s" > "%t"
// RUN: %exits-with 4 %dafny /arith:10 "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

// When multiplication is axiomatized to include associativity of Mul
// (which is the case with /arith:10), then one can run into a matching loop.
// To try to prevent this, Dafny's axiom for Mul-associativity has an
// antecedent. These tests would cause a matching loop without that antecedent.

lemma Test0(one: int, forty_two: int)
  requires forty_two == one * forty_two
  ensures false
{ // error: postcondition violation (should not cause verifier to loop forever)
}

lemma Test1(one: int, forty_two: int)
  requires forty_two == forty_two * one
  ensures false
{ // error: postcondition violation (should not cause verifier to loop forever)
}
