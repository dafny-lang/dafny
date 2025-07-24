// RUN: %run %s &> "%t"
// RUN: %diff "%s.expect" "%t"

ghost method foo(arr: array<int>) 
  modifies arr
  requires arr.Length > 1
{
  arr[0] := 3;
}

method bar(arr: array<int>) 
  modifies arr
  requires arr.Length > 1
{
  arr[0] := 3;
}