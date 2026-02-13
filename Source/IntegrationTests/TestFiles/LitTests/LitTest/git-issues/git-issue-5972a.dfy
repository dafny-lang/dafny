// RUN: %exits-with 2 %verify --type-system-refresh --general-newtypes "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This module is like SubsetTypes in git-issue-5972.dfy, but uses newtypes around the map/seq types
module Newtypes {
  newtype MyMap<T, U> = map<T, U>
  newtype MySeq<T> = seq<T>

  datatype M<T, U> = M(m: MyMap<T, U>)

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
    return m1 == m2; // error: the types of m1 and m2 do not support equality
  }

  datatype S<T> = S(s: MySeq<T>)

  method CompareAnythingS<A>(f: A, g: A) returns (b: bool) 
    ensures b <==> f == g
  {
    var m1 := S([f]);
    var m2 := S([g]);
    assert m1 == m2 <==> f == g by {
      if f == g {
        assert m1 == m2;
      }
      if m1 == m2 {
        assert m1.s[0] == m2.s[0];
      }
    }
    return m1 == m2; // error: the types of m1 and m2 do not support equality
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
}

// This module is like Newtypes above, but the two newtypes are declared to definitely support equality.
// The fact that their RHSs don't gives rise to errors. This was not properly handled before the fix
// of issue 5972.
module NewtypesWithGuaranteedEqualitySupport {
  type MyMap(==)<T, U> = map<T, U> // error: RHS does not support equality as promised
  type MySeq(==)<T> = seq<T> // error: RHS does not support equality as promised

  datatype M<T, U> = M(m: MyMap<T, U>)

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

  datatype S<T> = S(s: MySeq<T>)

  method CompareAnythingS<A>(f: A, g: A) returns (b: bool) 
    ensures b <==> f == g
  {
    var m1 := S([f]);
    var m2 := S([g]);
    assert m1 == m2 <==> f == g by {
      if f == g {
        assert m1 == m2;
      }
      if m1 == m2 {
        assert m1.s[0] == m2.s[0];
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

  method Test() {
    var s1 := Stream.From(0);
    var s2 := Stream.From(0);
    var b := CompareAnything(s1, s2);
    var b2 := CompareAnythingS(s1, s2);
    if !b || !b2 {
      assert false;
      print 1/0;
    }
  }
}
