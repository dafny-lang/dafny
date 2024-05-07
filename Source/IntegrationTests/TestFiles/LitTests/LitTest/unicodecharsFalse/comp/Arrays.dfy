// NONUNIFORM: https://github.com/dafny-lang/dafny/issues/2582
// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment --allow-warnings --unicode-char false
include "../../comp/Arrays.dfy"
