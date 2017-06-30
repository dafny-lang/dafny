// RUN: %dafny /rprint:"%t.rprint" /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "git-issue64.dfyi"

function id(x:word): word { x }
