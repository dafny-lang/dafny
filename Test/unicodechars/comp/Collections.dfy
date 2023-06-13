// NONUNIFORM:
// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment --spill-translation --unicode-char:true --verify-included-files
include "../../comp/Collections.dfy"
