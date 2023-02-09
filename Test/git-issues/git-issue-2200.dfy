// RUN: %resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function f(i: int): int { 42 }

function g(): int { f(1,2) }
