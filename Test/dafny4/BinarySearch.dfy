// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Binary search using standard integers

method BinarySearch(a: array<int>, key: int) returns (r: int)
  requires forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures 0 <= r ==> r < a.Length && a[r] == key
  ensures r < 0 ==> key !in a[..]
{
  var lo, hi := 0, a.Length;
  while lo < hi
    invariant 0 <= lo <= hi <= a.Length
    invariant key !in a[..lo] && key !in a[hi..]
  {
    var mid := (lo + hi) / 2;
    if key < a[mid] {
      hi := mid;
    } else if a[mid] < key {
      lo := mid + 1;
    } else {
      return mid;
    }
  }
  return -1;
}

// Binary search using bounded integers

newtype int32 = x | -0x8000_0000 <= x < 0x8000_0000

method BinarySearchInt32_bad(a: array<int>, key: int) returns (r: int32)
  requires a.Length < 0x8000_0000
  requires forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures 0 <= r ==> r < a.Length as int32 && a[r] == key
  ensures r < 0 ==> key !in a[..]
{
  var lo, hi := 0, a.Length as int32;
  while lo < hi
    invariant 0 <= lo <= hi <= a.Length as int32
    invariant key !in a[..lo] && key !in a[hi..]
  {
    var mid := (lo + hi) / 2;  // error: possible overflow
    if key < a[mid] {
      hi := mid;
    } else if a[mid] < key {
      lo := mid + 1;
    } else {
      return mid;
    }
  }
  return -1;
}

method BinarySearchInt32_good(a: array<int>, key: int) returns (r: int32)
  requires a.Length < 0x8000_0000
  requires forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures 0 <= r ==> r < a.Length as int32 && a[r] == key
  ensures r < 0 ==> key !in a[..]
{
  var lo, hi := 0, a.Length as int32;
  while lo < hi
    invariant 0 <= lo <= hi <= a.Length as int32
    invariant key !in a[..lo] && key !in a[hi..]
  {
    var mid := lo + (hi - lo) / 2;  // this is how to do it
    if key < a[mid] {
      hi := mid;
    } else if a[mid] < key {
      lo := mid + 1;
    } else {
      return mid;
    }
  }
  return -1;
}
