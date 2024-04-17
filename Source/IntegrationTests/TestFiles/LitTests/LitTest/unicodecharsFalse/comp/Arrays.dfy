// NONUNIFORM: https://github.com/dafny-lang/dafny/issues/2582
// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment --allow-warnings --unicode-char false --verify-included-files
include "../../comp/Arrays.dfy"
