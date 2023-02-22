// RUN: %baredafny verify --use-basename-for-filename "%s" > "%t"
// RUN: ! %baredafny run --use-basename-for-filename "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

function method Foo(): int ensures false; ensures false;
function method {:axiom} Bar(): int ensures false;
function method {:extern} Baz(): int ensures false;
function method Fonk(): int ensures {:axiom} false;

trait Far {
  function method Foo(): int
}
