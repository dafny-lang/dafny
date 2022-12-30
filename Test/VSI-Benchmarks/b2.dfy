// RUN: %baredafny verify %args --relax-definite-assignment "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Benchmark2 {
  method BinarySearch(a: array<int>, key: int) returns (result: int)
    requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j];
    ensures -1 <= result < a.Length;
    ensures 0 <= result ==> a[result] == key;
    ensures result == -1 ==> forall i :: 0 <= i < a.Length ==> a[i] != key;
  {
    var low := 0;
    var high := a.Length;

    while (low < high)
      invariant 0 <= low <= high <= a.Length;
      invariant forall i :: 0 <= i < low ==> a[i] < key;
      invariant forall i :: high <= i < a.Length ==> key < a[i];
    {
      var mid := low + (high - low) / 2;
      var midVal := a[mid];

      if (midVal < key) {
        low := mid + 1;
      } else if (key < midVal) {
        high := mid;
      } else {
        result := mid; // key found
        return;
      }
    }
    result := -1;  // key not present
  }
}

method Main() {
  var a := new int[5];
  a[0] := -4;
  a[1] := -2;
  a[2] := -2;
  a[3] := 0;
  a[4] := 25;
  TestSearch(a, 4);
  TestSearch(a, -8);
  TestSearch(a, -2);
  TestSearch(a, 0);
  TestSearch(a, 23);
  TestSearch(a, 25);
  TestSearch(a, 27);
}

method TestSearch(a: array<int>, key: int)
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j];
{
  var b := new Benchmark2;
  var r := b.BinarySearch(a, key);
  print "Looking for key=", key, ", result=", r, "\n";
}
