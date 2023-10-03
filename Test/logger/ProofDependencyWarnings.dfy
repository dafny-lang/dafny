// RUN: %verify --warn-contradictory-assumptions --warn-redundant-assumptions --verify-included-files "%s" > "%t"
// RUN: %diff "%t" "%s.expect"

include "ProofDependencyLogging.dfy"
