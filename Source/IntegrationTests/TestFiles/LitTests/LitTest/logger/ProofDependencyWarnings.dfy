// RUN: %baredafny verify --use-basename-for-filename --show-snippets false --verify-included-files --warn-contradictory-assumptions --warn-redundant-assumptions "%s" > "%t.new"
// RUN: %diff "%s.expect" "%t.new"
// RUN: %baredafny /compile:0 /useBaseNameForFileName /verifyAllModules /warnContradictoryAssumptions /warnRedundantAssumptions "%s" > "%t.old"
// RUN: %diff "%s.expect" "%t.old"

include "ProofDependencies.dfy"
