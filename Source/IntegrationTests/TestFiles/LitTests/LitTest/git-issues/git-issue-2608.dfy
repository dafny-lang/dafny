// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment

method GetNext(i: int) returns (j: int, possible: bool) {
  if i == 1 {
    possible := false;
    j := 0;
  } else {
    possible := true;
    j := if i % 2 == 0 then  i / 2 else i * 3 + 1;
  }
}

method Main()
{
  var i := 10;
  var k := 27;
  while i > 0
    invariant i >= 0
  {
    label before:
    var newK, possible := GetNext(k);
    if(!possible) {
      break;
    }
    k := newK;
    print k;
    i := i - 1;
  }
}
