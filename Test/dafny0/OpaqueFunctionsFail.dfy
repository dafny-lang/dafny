// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /rewriteOpaqueUseFuel:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


// ---------------------------------- opaque and generics

// This function cannot normally be called, so the
// generated opaquity code contains such a bad call.
function{:opaque} zero<A>():int { 0 }

