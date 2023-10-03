// RUN: %verify --verify-included-files --warn-contradictory-assumptions --warn-redundant-assumptions "%s" > "%t"
// RUN: %diff "%t" "%s.expect"

include "ProofDependencyLogging.dfy"
