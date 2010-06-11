
class Benchmark2 {
  method BinarySearch(a: array<int>, key: int) returns (result: int)
    requires a != null;
    requires (forall i, j :: 0 <= i && i < j && j < |a| ==> a[i] <= a[j]);
    ensures -1 <= result && result < |a|;
    ensures 0 <= result ==> a[result] == key;
    ensures result == -1 ==> (forall i :: 0 <= i && i < |a| ==> a[i] != key);
  {
    var low := 0;
    var high := |a|;

    while (low < high)
      invariant 0 <= low && low <= high && high <= |a|;
      invariant (forall i :: 0 <= i && i < low ==> a[i] < key);
      invariant (forall i :: high <= i && i < |a| ==> key < a[i]);
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
  call TestSearch(a, 4);
  call TestSearch(a, -8);
  call TestSearch(a, -2);
  call TestSearch(a, 0);
  call TestSearch(a, 23);
  call TestSearch(a, 25);
  call TestSearch(a, 27);
}

method TestSearch(a: array<int>, key: int)
  requires a != null;
  requires (forall i, j :: 0 <= i && i < j && j < |a| ==> a[i] <= a[j]);
{
  var b := new Benchmark2;
  call r := b.BinarySearch(a, key);
  print "Looking for key=", key, ", result=", r, "\n";
}
