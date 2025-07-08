// RUN: %testDafnyForEachResolver "%s" -- --allow-warnings


datatype d = D(i:int)
ghost predicate p(s:int, y:int)
ghost predicate q(d:d) { exists s :: (match d case D(z) => p(s, z)) }

