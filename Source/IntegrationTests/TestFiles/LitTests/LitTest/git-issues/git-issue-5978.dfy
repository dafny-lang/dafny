// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// RUN: %exits-with 2 %baredafny verify --type-system-refresh --general-newtypes %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype M<U> = m: map<int, U> | true

method CompareAnything<A>(f: A, g: A) returns (b: bool) 
   ensures b <==> f == g
{
  var m1 := map[0 := f] as M<A>;
  var m2 := map[0 := g] as M<A>;
  assert m1 == m2 <==> f == g by {
    if f == g {
      assert m1 == m2;
    }
    if m1 == m2 {
      assert m1[0] == m2[0];
    }
  }
  return m1 == m2;
}

newtype S<T> = s: seq<T> | true

method CompareAnythingS<A>(f: A, g: A) returns (b: bool) 
   ensures b <==> f == g
{
  var m1 := [f] as S<A>;
  var m2 := [g] as S<A>;
  assert m1 == m2 <==> f == g by {
    if f == g {
      assert m1 == m2;
    }
    if m1 == m2 {
      assert m1[0] == m2[0];
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
  var b2 := CompareAnythingS(s1, s2);
  if !b || !b2 {
    assert false;
    print 1/0;
  }
}