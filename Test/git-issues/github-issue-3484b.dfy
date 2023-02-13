// RUN: ! %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function Bar(x: int): int {
  match x {
  }
}