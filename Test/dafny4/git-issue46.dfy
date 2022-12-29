// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "git-issue46-include.dfyi"

module m4 refines m2 { }


