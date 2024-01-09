// RUN: %verify --allow-axioms:false "%s" > "%t"
// RUN: ! %run --allow-axioms:false "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

function Foo(): int ensures false ensures false
function {:axiom} Bar(): int ensures false
function {:extern} Baz(): int ensures false
function Fonk(): int ensures {:axiom} false
function Faz(): int

trait Far {
  function Foo(): int
}
