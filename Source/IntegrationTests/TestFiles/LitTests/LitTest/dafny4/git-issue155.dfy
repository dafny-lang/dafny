// RUN: %testDafnyForEachResolver "%s"


datatype A = A0
datatype B = B0

ghost function F(a: A, b: B): int
{
  match (a, b)
  case (A0, B0) => 0
}

method M(a: A, b: B)
{
  match (a, b)
  case (A0, B0) =>
}