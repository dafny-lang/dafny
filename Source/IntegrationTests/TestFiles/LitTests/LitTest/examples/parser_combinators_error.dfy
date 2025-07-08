// RUN: %exits-with 2 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function Apply(f: () -> int): int { f() }

function F0(): int { Apply(F0) } // error: cannot use F0 naked here
