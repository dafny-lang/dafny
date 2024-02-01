// RUN: %baredafny verify --use-basename-for-filename --show-snippets false --verify-included-files --warn-contradictory-assumptions --warn-redundant-assumptions "%s" > "%t"
// RUN: %diff "%s.expect" "%t" 

include "ProofDependencies.dfy"
