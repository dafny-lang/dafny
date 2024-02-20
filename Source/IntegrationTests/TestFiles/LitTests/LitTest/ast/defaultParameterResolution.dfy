// RUN: %testDafnyForEachResolver "%s" --expect-exit-code=2

function SumFromTo(sequence: nat -> real, start: nat := 0, end: nat): real

function PartialSums(sequence: nat -> real): nat -> real {
  (n: nat) => SumFromTo(sequence, n)
}