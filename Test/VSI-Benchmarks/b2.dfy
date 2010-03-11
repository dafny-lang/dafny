
// Note:  There is a bug in the well-formedness of functions.  In particular,
// it doesn't look at the requires clause (in the proper way).  Fixed!
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
      invariant 0 <= low && high <= a.Length();
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
  method Init(n: int);
    requires 0 <= n;
    modifies this;
    ensures |contents| == n;
  function method Length(): int
    reads this;
  { |contents| }
  function method Get(i: int): int
    requires 0 <= i && i < |contents|;
    reads this;
  { contents[i] }
  method Set(i: int, x: int);
    requires 0 <= i && i < |contents|;
    modifies this;
    ensures contents[..i] == old(contents[..i]);
    ensures contents[i] == x;
    ensures contents[i+1..] == old(contents[i+1..]);
}
