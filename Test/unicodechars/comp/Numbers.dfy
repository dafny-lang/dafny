// NONUNIFORM: https://github.com/dafny-lang/dafny/issues/4174
// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment --unicode-char:true --verify-included-files
include "../../comp/Numbers.dfy"
