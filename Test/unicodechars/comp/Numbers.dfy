// NONUNIFORM: https://github.com/dafny-lang/dafny/issues/4108
// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment --unicode-char:true --verify-included-files
include "../../comp/Numbers.dfy"
