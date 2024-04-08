// RUN: %testDafnyForEachResolver "%s" -- --allow-axioms=false
// NONUNIFORM: warning will be the same for all back-end

type Even = x: int | x % 2 == 0
opaque const {:axiom} ten: Even := 10