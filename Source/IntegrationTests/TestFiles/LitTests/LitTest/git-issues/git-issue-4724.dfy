// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type seq31<T> = x: seq<T> | |x| <= 31

method TakeThis(x: seq31<int> := []) 
{
  TakeThis(); // Error: cannot prove termination; try supplying a decreases clause
}