// NONUNIFORM: https://github.com/dafny-lang/dafny/issues/4108
// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment --allow-deprecation --unicode-char false --spill-translation --verify-included-files
include "../../comp/Collections.dfy"
