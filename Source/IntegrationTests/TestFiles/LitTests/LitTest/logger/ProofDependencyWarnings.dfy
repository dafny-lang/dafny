// RUN: %baredafny verify --use-basename-for-filename --allow-axioms --show-snippets false --verify-included-files --warn-contradictory-assumptions --warn-redundant-assumptions --allow-warnings "%s" > "%t.new"
// RUN: %diff "%s.expect" "%t.new"

include "ProofDependencies.dfy"
