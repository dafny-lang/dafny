// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "git-issue64.dfyi"

function id(x:word): word { x }
