// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype d = D(i:int)
ghost predicate p(s:int, y:int)
ghost predicate q(d:d) { exists s :: (match d case D(z) => p(s, z)) }

