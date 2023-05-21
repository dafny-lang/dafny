// RUN: %exits-with 1 %baredafny build -t:lib "%s" x.doo > "%t"
// RUN: %diff "%s.expect" "%t"

const c := 5


