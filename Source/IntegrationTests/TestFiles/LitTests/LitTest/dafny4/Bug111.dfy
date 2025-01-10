// RUN: %testDafnyForEachResolver "%s"


datatype A = A(i:int)
datatype B = B1(a1:A) | B2(a2:A)

ghost function f(b:B):int
{
  match b
  {
    case B1(A(i)) => i
    case B2(A(j)) => j
  }
}




