// NONUNIFORM: https://github.com/dafny-lang/dafny/issues/4108
// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment --unicode-char:true /verifyAllModules
include "../../comp/Numbers.dfy"
