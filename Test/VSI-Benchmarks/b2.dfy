
// Note:Implemented arrays as Dafny does not provide them

class Benchmark2 {
  method BinarySearch(a: Array, key: int) returns (result: int)
    requires a != null;
    requires (forall i, j ::
                0 <= i && i < j && j < a.Length() ==> a.Get(i) <= a.Get(j));
    ensures -1 <= result && result < a.Length();
    ensures 0 <= result ==> a.Get(result) == key;
    ensures result == -1 ==>
              (forall i :: 0 <= i && i < a.Length() ==> a.Get(i) != key);
  {
    var low := 0;
    var high := a.Length();

    while (low < high)
      invariant 0 <= low && low <= high && high <= a.Length();
      invariant (forall i :: 0 <= i && i < low ==> a.Get(i) < key);
      invariant (forall i :: high <= i && i < a.Length() ==> key < a.Get(i));
      decreases high - low;
    {
      var mid := low + (high - low) / 2;
      var midVal := a.Get(mid);

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

class Array {
  var contents: seq<int>;
  method Init(n: int)
    requires 0 <= n;
    modifies this;
    ensures |contents| == n;
  {
    var i := 0;
    contents := [];
    while (i < n)
      invariant i <= n && i == |contents|;
      decreases n - i;
    {
      contents := contents + [0];
      i := i + 1;
    }
  }
   function method Length(): int
    reads this;
  { |contents| }
   function method Get(i: int): int
    requires 0 <= i && i < |contents|;
    reads this;
  { contents[i] }
  method Set(i: int, x: int)
    requires 0 <= i && i < |contents|;
    modifies this;
    ensures contents == old(contents)[i := x];
  {
    contents := contents[i := x];
  }
}

method Main() {
  var a := new Array;
  call a.Init(5);
  call a.Set(0, -4);
  call a.Set(1, -2);
  call a.Set(2, -2);
  call a.Set(3, 0);
  call a.Set(4, 25);
  call TestSearch(a, 4);
  call TestSearch(a, -8);
  call TestSearch(a, -2);
  call TestSearch(a, 0);
  call TestSearch(a, 23);
  call TestSearch(a, 25);
  call TestSearch(a, 27);
}

method TestSearch(a: Array, key: int)
  requires a != null;
  requires (forall i, j :: 0 <= i && i < j && j < a.Length() ==> a.Get(i) <= a.Get(j));
{
  var b := new Benchmark2;
  call r := b.BinarySearch(a, key);
  print "Looking for key=", key, ", result=", r, "\n";
}
