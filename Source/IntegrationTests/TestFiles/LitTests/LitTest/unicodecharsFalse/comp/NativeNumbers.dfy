// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment --spill-translation --allow-deprecation --unicode-char false --verify-included-files --enforce-determinism
// Skip JavaScript because JavaScript doesn't have the same native types

include "../../comp/NativeNumbers.dfy"
