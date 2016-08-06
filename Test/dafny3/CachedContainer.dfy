// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// give the method signatures and specs
abstract module M0 {
  class {:autocontracts} Container<T(==)> {
    ghost var Contents: set<T>
    protected predicate Valid()
    constructor ()
      ensures Contents == {}
    method Add(t: T)
      ensures Contents == old(Contents) + {t}
    method Remove(t: T)
      ensures Contents == old(Contents) - {t}
    method Contains(t: T) returns (b: bool)
      ensures Contents == old(Contents)
      ensures b <==> t in Contents
  }
}

// provide bodies for the methods
abstract module M1 refines M0 {
  class Container<T(==)> {
    constructor... {
      Contents := {};
      Repr := {this};
    }
    method Add... {
      Contents := Contents + {t};
    }
    method Remove... {
      Contents := Contents - {t};
    }
    method Contains... {
      // b := t in Contents;
      b :| assume b <==> t in Contents;
    }
  }
}

// implement the set in terms of a sequence
module M2 refines M1 {
  class Container<T(==)> {
    var elems: seq<T>;
    protected predicate Valid()
    {
      Contents == (set x | x in elems) &&
      forall i,j :: 0 <= i < j < |elems| ==> elems[i] != elems[j]
    }
    method FindIndex(t: T) returns (j: nat)
      ensures j <= |elems|
      ensures if j < |elems| then elems[j] == t else t !in elems
    {
      j := 0;
      while (j < |elems|)
        invariant j <= |elems|
        invariant forall i :: 0 <= i < j ==> elems[i] != t
      {
        if (elems[j] == t) {
          return;
        }
        j := j + 1;
      }
    }

    constructor... {
      elems := [];
    }
    method Add... {
      var j := FindIndex(t);
      if (j == |elems|) {
        elems := elems + [t];
      }
    }
    method Remove... {
      var j := FindIndex(t);
      if (j < |elems|) {
        elems := elems[..j] + elems[j+1..];
      }
    }
    method Contains... {
      var j := FindIndex(t);
      b := j < |elems|;
    }
  }
}

// implement a cache
module M3 refines M2 {
  class Container<T(==)> {
    var cachedValue: T;
    var cachedIndex: int;
    protected predicate Valid() {
      0 <= cachedIndex ==> cachedIndex < |elems| && elems[cachedIndex] == cachedValue
    }
    constructor... {
      cachedIndex := -1;
    }
    method FindIndex... {
      if (0 <= cachedIndex && cachedValue == t) {
        return cachedIndex;
      }
    }
    method Remove... {
      ...;
      if ... {
        if (cachedIndex == j) {
          // clear the cache
          cachedIndex := -1;
        } else if (j < cachedIndex) {
          // adjust for the shifting down
          cachedIndex := cachedIndex - 1;
        }
      }
    }
  }
}

// here a client of the Container
module Client {
  import M as M0 default M2
  method Test() {
    var c := new M.Container();
    c.Add(56);
    c.Add(12);
    var b := c.Contains(17);
    assert !b;
    b := c.Contains(12);
    assert b;
    c.Remove(12);
    b := c.Contains(12);
    assert !b;
    assert c.Contents == {56};
  }
}

module CachedClient refines Client {
  import M = M3
  method Main() {
    Test();
  }
}
