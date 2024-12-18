// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"

module Issue5972 {
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
    return m1 == m2; // error: the types of m1 and m2 do not support equality
  }

  datatype S<T> = S(s: seq<T>)

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

// This module is like Issue5972 above, but uses type synonyms around the map/seq types
module TypeSynonyms {
  type MyMap<T, U> = map<T, U>
  type MySeq<T> = seq<T>

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

// This module is like TypeSynonyms above, but the two type synonyms are declared to definitely support equality.
// The fact that their RHSs don't gives rise to errors, but in the process of fixing issue 5972, this program
// had caused a crash, so it seems good to include as a test case.
module TypeSynonymsWithGuaranteedEqualitySupport {
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

// This module is like TypeSynonyms above, but uses subset types around the map/seq types
module SubsetTypes {
  type MyMap<T, U> = m: map<T, U> | true
  type MySeq<T> = s: seq<T> | true

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
