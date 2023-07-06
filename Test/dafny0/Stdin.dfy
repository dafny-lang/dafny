// RUN: %exits-with 0 %stdin "module A{}" %baredafny verify --show-snippets:false --stdin > "%t"
// RUN: %exits-with 4 %stdin "method a() { assert false; }" %baredafny verify --show-snippets:false --stdin >> "%t"
// RUN: %diff "%s.expect" "%t"

