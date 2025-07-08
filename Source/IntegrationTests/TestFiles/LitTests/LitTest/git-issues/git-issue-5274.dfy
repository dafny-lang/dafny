// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"

datatype Pair<T(==)> = MakePair(0: T, 1: T) {
  function Same(): bool {
    this.0 == this.1
  }
}

method ReturnFalse() returns (b: bool)
  ensures !b
{
  var c := (2, ghost 5);
  var d := (2, ghost 6);
  assert c != d;
  b := MakePair(c, d).Same(); // error: uses the type Pair incorrectly

  print MakePair(c, d); // error: uses the type Pair incorrectly
  print "\n";
}

method Main() {
  var b := ReturnFalse();
  if b {
    // we should never get here
    print 10 / 0;
  }
}
