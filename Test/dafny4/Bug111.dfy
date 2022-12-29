// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype A = A(i:int)
datatype B = B1(a1:A) | B2(a2:A)

function f(b:B):int
{
  match b
  {
    case B1(A(i)) => i
    case B2(A(j)) => j
  }
}




