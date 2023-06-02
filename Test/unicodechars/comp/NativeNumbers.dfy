// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment --spill-translation --unicode-char:true /verifyAllModules
// Skip JavaScript because JavaScript doesn't have the same native types

include "../../comp/NativeNumbers.dfy"
