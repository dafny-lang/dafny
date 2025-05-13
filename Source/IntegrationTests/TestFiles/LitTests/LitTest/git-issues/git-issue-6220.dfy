// Bug originated from the C# backend, but might as well try every backend
// RUN: %testDafnyForEachCompiler "%s"

newtype uint64 = x: int | 0 <= x < 0x1_00000000_00000000

function Fill<T>(value: T, n: uint64): seq<T>
  ensures |Fill(value, n)| == n as nat
  ensures forall i :: 0 <= i < n ==> Fill(value, n)[i] == value
{
  seq(n, _ => value)
}

method Main()
{
  var ss := Fill('a', 42);
  print ss, "\n";
}