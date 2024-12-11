// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype M<T, U> = M(m: map<T, U>)

method CompareAnything<A>(f: A, g: A) returns (b: bool) 
   ensures b <==> f == g
{
  var m1 := M(map[0 := f]);
  var m2 := M(map[0 := g]);
  assert m1 == m2 <==> f == g by {
    if f == g {
      assert m1 == m2;
    }
    if m1 == m2 {
      assert m1.m[0] == m2.m[0];
    }
  }
  return m1 == m2;
}

codatatype Stream = Stream(head: int, tail: Stream)
{
  static function From(i: int): Stream {
    Stream(i, From(i + 1))
  }
}

method Main() {
  var s1 := Stream.From(0);
  var s2 := Stream.From(0);
  var b := CompareAnything(s1, s2);
  if !b {
    assert false;
    print 1/0;
  }
}