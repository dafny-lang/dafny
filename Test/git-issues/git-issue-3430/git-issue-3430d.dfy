// RUN: %exits-with 2 %resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
}

module A.C {}
module A.C {}

// SHould report duplicate
