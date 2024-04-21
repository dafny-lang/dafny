// RUN: %baredafny verify --use-basename-for-filename --allow-axioms --show-snippets false --verify-included-files --warn-contradictory-assumptions --warn-redundant-assumptions --allow-warnings "%s" > "%t.new"
// RUN: %diff "%s.expect" "%t.new"
// Also test old CLI
// RUN: %baredafny /compile:0 /useBaseNameForFileName /verifyAllModules /warnContradictoryAssumptions /warnRedundantAssumptions "%s" > "%t.old"
// RUN: %diff "%s.expect2" "%t.old"

include "ProofDependencies.dfy"
