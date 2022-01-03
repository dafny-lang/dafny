// RUN: %dafny /compile:3 /rprint:"%t.rprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "../libraries/src/Wrappers.dfy"
import opened Wrappers

method id<T>() returns (r: T)  {
}

method test() returns (r: Option<int>) {
  var x :- id<Option<int>>();
  r := None;
}