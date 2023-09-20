// RUN: %baredafny verify --log-format:text --warn-contradictory-assumptions --warn-redundant-assumptions "%s" > "%t"
// %diff "%t" "%s.expect"

include "ProofDependencyLogging.dfy"
