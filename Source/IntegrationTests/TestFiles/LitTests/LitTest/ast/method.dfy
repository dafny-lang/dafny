// RUN: %verify --allow-axioms:false --type-system-refresh --allow-warnings "%s" > "%t"
// RUN: %verify --allow-axioms:false --type-system-refresh --allow-external-contracts --allow-warnings "%s" >> "%t"
 
// NONUNIFORM: warning will be the same for all back-ends
// RUN: ! %run --allow-axioms:false "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Compiled() ensures false ensures false
ghost method Ghost() ensures false ensures false
method {:axiom} Axiom() ensures false
ghost method {:axiom} GhostAxiom() ensures false
method {:extern} Extern() ensures false
ghost method {:extern} GhostExtern() ensures false
method {:axiom} {:extern} AxiomExtern() ensures false
ghost method {:axiom} {:extern} GhostAxiomExtern() ensures false

method BodylessLoop() ensures false {
  while(true) invariant true || false
}

method {:verify false} Brap() {
  assert false;
}

method {:extern} Brrr() ensures false
method {:extern} Booo() requires false {
  assert false;
}
