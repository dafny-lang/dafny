// RUN: ! %baredafny verify %args --library=%S/Inputs/brokenProducer.dfy "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function Foo(): int {
  Bar()
}
