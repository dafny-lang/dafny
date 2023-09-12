// RUN: %baredafny verify --log-format:text --warn-vacuity --warn-redundant-assumptions "%s" > "%t"
// %diff "%t" "%s.expect"

include "ProofDependencyLogging.dfy"
