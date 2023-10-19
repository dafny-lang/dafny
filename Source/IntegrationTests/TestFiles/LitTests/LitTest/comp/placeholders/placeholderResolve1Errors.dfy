// RUN: ! %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

placeholder module Cycle1 replaces Cycle2 {
}

placeholder module Cycle2 replaces Cycle1 {
}