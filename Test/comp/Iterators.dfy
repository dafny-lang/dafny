/*
---
!dafnyTestSpec
compileTargetOverrides:
    java:
        expected:
            exitCode: 134
            outputFile: ~
            specialCaseReason: Iterators are not implemented for Java
*/
class C {
  var x: int
  // for variety, the following tests the use of an instance Main method
  method Main(ghost u: int) returns (ghost r: bool, ghost s: bool) {
    print "hello, instance\n";
    print "x is ", x, "\n";
    Client();
  }
}

iterator Iter<X(==,0)>(a: array<X>, stop: X) yields (x: X)
  yield ensures |xs| <= a.Length
  ensures |xs| <= a.Length
{
  var i := 0;
  while i < a.Length
    invariant |xs| == i <= a.Length
  {
    if i % 2 == 0 {
      yield a[i];
    }
    x := a[i];
    if x == stop {
      break;
    }
    if i % 2 == 1 {
      yield;
    }
    i := i + 1;
  }
}

method Client()
{
  var a := new real[6](i => i as real);

  var iter := new Iter(a, 2.4);
  while true
    invariant iter.Valid() && fresh(iter._new)
    decreases a.Length - |iter.xs|
  {
    var more := iter.MoveNext();
    if (!more) { break; }
    print iter.x, " ";
  }
  print "\n";

  iter := new Iter(a, 2.0);
  while true
    invariant iter.Valid() && fresh(iter._new)
    decreases a.Length - |iter.xs|
  {
    var more := iter.MoveNext();
    if (!more) { break; }
    print iter.x, " ";
  }
  print "\n";
}
