// RUN: ! %verify %s > %t
// RUN: %diff "%s.expect" "%t"

datatype Type = 
  | Cons()

datatype Test = Test(
  y: Type,
  y: Type  // error: duplicate member name
) 

predicate pred(t: Test, t': Test)
{
  && t' == t.(y := Cons())
}

datatype ZTest = ZTest(
  z: real,
  z: ThisTypeDoesNotExist // error: duplicate member name
) 
