// RUN: %baredafny verify --use-basename-for-filename "%s" > "%t"
// RUN: ! %baredafny run --use-basename-for-filename "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

function method Foo(): int
function method {:axiom} Bar(): int
function method {:extern} Baz(): int

trait Far {
  function method Foo(): int
}
