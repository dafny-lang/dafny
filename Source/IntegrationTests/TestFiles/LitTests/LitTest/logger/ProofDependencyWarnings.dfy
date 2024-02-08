// RUN: %verify --verify-included-files --warn-contradictory-assumptions --warn-redundant-assumptions "%s" > "%t.new"
// RUN: %diff "%s.expect" "%t.new"
// RUN: %baredafny /compile:0 /useBaseNameForFileName /verifyAllModules /warnContradictoryAssumptions /warnRedundantAssumptions "%s" > "%t.old"
// RUN: %diff "%s.expect" "%t.old"
// RUN: %exits-with 4 %verify --verify-included-files --warn-contradictory-assumptions --warn-redundant-assumptions --warn-as-errors "%s"

include "ProofDependencies.dfy"
