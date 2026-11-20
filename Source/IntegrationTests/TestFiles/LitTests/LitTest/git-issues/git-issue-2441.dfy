// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment --enforce-determinism

datatype A = A(B: B)
datatype B = X
