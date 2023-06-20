// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment

datatype A = A(B: B)
datatype B = X
