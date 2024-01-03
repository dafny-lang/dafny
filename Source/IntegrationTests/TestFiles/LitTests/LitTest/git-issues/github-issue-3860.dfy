// RUN: ! %verify %s > %t
// RUN: %diff "%s.expect" "%t"

datatype Type = 
  | Cons()

datatype Test = Test(
  y : Type,
  y : Type
) 

predicate pred(t: Test, t': Test)
{
  && t' == t.(y := Cons())
}