// RUN: %baredafny verify --function-syntax:4 --use-basename-for-filename "%s" > "%t"
// RUN: ! %baredafny run --function-syntax:4 --use-basename-for-filename "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

function Foo(): int ensures false; ensures false;
function {:axiom} Bar(): int ensures false;
function {:extern} Baz(): int ensures false;
function Fonk(): int ensures {:axiom} false;
function Faz(): int

trait Far {
  function Foo(): int
}
