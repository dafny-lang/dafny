// RUN: %baredafny verify %args --default-function-opacity autoRevealDependencies "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function two() : int { 2 }
datatype t = Nat(val :nat := two())
