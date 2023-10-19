// RUN: %testDafnyForEachCompiler "%s"
const TWO_TO_THE_64:  int := 0x1_00000000_00000000
newtype uint64 = x: int | 0 <= x < TWO_TO_THE_64

method Foo() returns (tuple: (uint64, uint64)) {
  var s := [1,2,3];
  var (foo, length) := (0, |s| as uint64);
  return (foo, length);
}
