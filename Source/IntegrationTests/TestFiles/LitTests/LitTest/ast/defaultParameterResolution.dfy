// RUN: ! %resolve %s --type-system-refresh > %t
// RUN: ! %resolve %s >> %t
// RUN: %diff "%s.expect" "%t"

function SumFromTo(sequence: nat -> real, start: nat := 0, end: nat): real

function PartialSums(sequence: nat -> real): nat -> real {
  (n: nat) => SumFromTo(sequence, n)
}