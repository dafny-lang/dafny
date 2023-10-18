// RUN: %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "git-issue46-include.dfyi"

module m4 refines m2 { }


