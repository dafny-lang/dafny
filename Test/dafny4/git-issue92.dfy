// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype d = D(i:int)
predicate p(s:int, y:int)
predicate q(d:d) { exists s :: (match d case D(z) => p(s, z)) }

