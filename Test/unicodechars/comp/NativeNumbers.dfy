// RUN: %testDafnyForEachCompiler "%s" --refresh-exit-code=0 -- --relax-definite-assignment --spill-translation --unicode-char:true --verify-included-files
// Skip JavaScript because JavaScript doesn't have the same native types

include "../../comp/NativeNumbers.dfy"
