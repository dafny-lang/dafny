
newtype int32 = x: int | 0 <= x < 0x1_0000_0000

method Main() {
  var x: seq<int32> := [1, 2, 3];
}