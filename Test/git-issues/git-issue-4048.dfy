// RUN: %exits-with 1 %baredafny build -t:lib "%s" x.doo 2> "%t"
// RUN: %diff "%s.expect" "%t"

// Tests case in which an input .doo file does not exist
const c := 5


