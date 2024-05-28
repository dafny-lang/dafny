// RUN: ! %verify --allow-axioms:false --type-system-refresh "%s" &> "%t"
// RUN: ! %verify --allow-axioms:false --type-system-refresh "%s" &>> "%t"
// NONUNIFORM: warning will be the same for all back-end
// RUN: ! %run --allow-axioms:false "%s" &>> "%t"
// RUN: %diff "%s.expect" "%t"


function Compiled(): int ensures false ensures false
ghost function Ghost(): int ensures false ensures false
function {:axiom} Axiom(): int ensures false
ghost function {:axiom} GhostAxiom(): int ensures false
function {:extern} Extern(): int ensures false
ghost function {:extern} GhostExtern(): int ensures false
function {:axiom} {:extern} AxiomExtern(): int ensures false
ghost function {:axiom} {:extern} GhostAxiomExtern(): int ensures false

function Fonk(): int ensures {:axiom} false

trait Far {
  function Foo(): int
}
