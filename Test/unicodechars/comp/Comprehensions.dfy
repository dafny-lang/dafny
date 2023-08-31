// NONUNIFORM: https://github.com/dafny-lang/dafny/issues/4108
// RUN: %testDafnyForEachCompiler "%s" --refresh-exit-code=0 -- --relax-definite-assignment --spill-translation --unicode-char:true --verify-included-files
include "../../comp/Comprehensions.dfy"
