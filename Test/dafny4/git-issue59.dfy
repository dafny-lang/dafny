// RUN: %exits-with 4 %dafny /tracePOs /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "git-issue59.dfyi"

method foo(x:byte) {
  var y:byte := x+1;
   }

