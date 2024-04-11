// RUN: %testDafnyForEachResolver "%s" -- --allow-axioms=false

type Even = x: int | x % 2 == 0
opaque const ten: Even := 10