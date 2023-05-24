// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

