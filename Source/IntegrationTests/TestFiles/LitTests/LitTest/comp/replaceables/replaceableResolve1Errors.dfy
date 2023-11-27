// RUN: ! %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

replaceable module Cycle1 replaces Cycle2 {
}

replaceable module Cycle2 replaces Cycle1 {
}