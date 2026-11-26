// RUN: %resolve --show-hints "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype T = x: int | -129 + (-4 % 2) <= x < 100
