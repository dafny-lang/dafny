// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type MyArray = array<int>
type MyMatrix = m: array2<int> | m.Length0 == m.Length1 witness *

class State
{  
  var arr: MyArray
  var m: MyMatrix
  var count: nat

  constructor () {
    arr, m := new int[100], new int[100, 100];
  }

  method Process(i: nat)
    requires i < arr.Length < m.Length0
    modifies this, arr, m
  {
    // two of the LHSs in the following assignment once caused the translator to crash
    arr[i], m[i, i], count := 0, 0, 0;
  }
}
