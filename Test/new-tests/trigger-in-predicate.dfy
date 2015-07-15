// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate A(x: bool, y: bool) { x }

predicate B(x: bool, z: bool) { forall y {:trigger A(x, y) } :: A(x, y) && z }

// Inlining is disabled here to prevent pollution of the trigger in B
method C() requires B(true || false, true) {}

// Inlining should work fine here
method C'() requires B(true, true) {}

// Inlining should work fine here
method C''() requires B(true, true && false) {}
