// RUN: %tobinary %s > %t.assertFalse.dbin
// RUN: %verify --input-format Binary %S/Inputs/additional.dfy --stdin < %t.assertFalse.dbin > %t
// RUN: %diff "%s.expect" "%t"

class BinarySearchValid {
  static function sorted(arr: array<int32>): bool
    reads arr
  {
    forall i: int32, j: int32 :: 
      !(0 <= i && i < j && j < arr.Length) || arr[i] < arr[j]
  }

  static method binarySearchImpl(arr: array<int32>, key: int32) returns (res: int32)
    requires arr.Length < 0x7fff_ffff
    requires sorted(arr)
    ensures (res == -1 && key !in arr[..]) || (0 <= res && res < arr.Length && arr[res] == key)
  {
    var lo: int32 := 0;
    var hi: int32 := arr.Length as int32;
    while lo < hi
      invariant 0 <= lo
      invariant lo <= hi
      invariant hi <= arr.Length
      invariant key !in arr[..lo]
      invariant key !in arr[hi..]
    {
      var mid: int32 := lo + (hi - lo) / 2;
      if key < arr[mid] {
        hi := mid;
      } else if arr[mid] < key {
        lo := mid + 1;
      } else {
        return mid;
      }
    }
    return -1;
  }
}
