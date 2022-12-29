// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

// This file contains an example chain of module refinements, starting from a
// simple interface M0 to an implementation M3. Module Client.Test() is
// verified against the original M0 module. Module CachedClient instantiates
// the abstract import of M0 with the concrete module M3, and then gets to
// reuse the proof done in Client.
//
// At a sufficiently abstract level, the concepts used are all standard.
// However, it can be tricky to set these things up in Dafny, if you want
// the final program to be a composition of smaller refinement steps.
//
// Textually, refinement modules in Dafny are written with "...", rather
// than by repeating the program text from the module being refined.
// This can be difficult to both author and read, so this file can be
// used as a guide for what to aim for. Undoubtedly, use of the /rprint:-
// option on the command line will be useful, since it lets you see what
// all the ...'s expand to.
//
// As a convenience, this program also uses a second experimental feature,
// namely the preprocessing requested by :autocontracts, which supplies
// much of the boilerplate specifications that one uses with the
// dynamic-frames idiom in Dafny. This feature was designed to reduce clutter
// in the program text, but can increase the mystery behind what's really
// going on. Here, too, using the /rprint:- option will be useful, since
// it shows the automatically generated specifications and code.
//
// (For another example that uses these features, see Test/dafny2/StoreAndRetrieve.dfy.)


// give the method signatures and specs
abstract module M0 {
  class {:autocontracts} Container<T(==)> {
    ghost var Contents: set<T>
    predicate Valid() {
      Valid'()
    }
    predicate {:autocontracts false} Valid'()
      reads this, Repr
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
  class Container<T(==)> ... {
    constructor... {
      Contents := {};
      Repr := {this};
      new;
      label CheckPost:
      assume Valid'();  // to be checked in further refinements
    }
    method Add... {
      Contents := Contents + {t};
      label CheckPost:
      assume Valid'();  // to be checked in further refinements
    }
    method Remove... {
      Contents := Contents - {t};
      label CheckPost:
      assume Valid'();  // to be checked in further refinements
    }
    method Contains... {
      // b := t in Contents;
      b :| assume b <==> t in Contents;
    }
  }
}

// implement the set in terms of a sequence
abstract module M2 refines M1 {
  class Container<T(==)> ... {
    var elems: seq<T>
    predicate Valid'...
    {
      Contents == (set x | x in elems) &&
      (forall i,j :: 0 <= i < j < |elems| ==> elems[i] != elems[j]) &&
      Valid''()
    }
    predicate {:autocontracts false} Valid''()
      reads this, Repr
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
      new;
      label CheckPost:
      assume Valid''();  // to be checked in further refinements
      assert ...;
    }
    method Add... {
      var j := FindIndex(t);
      if j == |elems| {
        elems := elems + [t];
      }
      ...;
      label CheckPost:
      assume Valid''();  // to be checked in further refinements
      assert ...;
    }
    method Remove... {
      var j := FindIndex(t);
      if j < |elems| {
        elems := elems[..j] + elems[j+1..];
      }
      ...;
      label CheckPost:
      assume Valid''();  // to be checked in further refinements
      assert ...;
    }
    method Contains... {
      var j := FindIndex(t);
      b := j < |elems|;
    }
  }
}

// implement a cache

module M3 refines M2 {
  datatype Cache<T> = None | Some(index: nat, value: T)
  class Container<T(==)> ... {
    var cache: Cache<T>
    predicate Valid''... {
      cache.Some? ==> cache.index < |elems| && elems[cache.index] == cache.value
    }
    constructor... {
      cache := None;
      new;
      ...;
      assert ...;
    }
    method FindIndex... {
      if cache.Some? && cache.value == t {
        return cache.index;
      }
    }
    method Add... {
      ...;
      assert ...;
    }
    method Remove... {
      ...;
      if ... {
        if cache.Some? {
          if cache.index == j {
            // clear the cache
            cache := None;
          } else if j < cache.index {
            // adjust for the shifting down
            cache := cache.(index := cache.index - 1);
          }
        }
      }
      ...;
      assert ...;
    }
  }
}

// here a client of the Container
abstract module Client {
  import M : M0
  method Test() {
    var c := new M.Container();
    c.Add(56);
    c.Add(12);
    var b := c.Contains(17);
    assert !b;
    print b, " ";  // false (does not contain 17)
    b := c.Contains(12);
    assert b;
    print b, " ";  // true (contains 12)
    c.Remove(12);
    b := c.Contains(12);
    assert !b;
    print b, " ";  // false (no longer contains 12)
    assert c.Contents == {56};
    b := c.Contains(56);
    assert b;
    print b, "\n";  // true (still contains 56)
  }
}

module CachedClient refines Client {
  import M = M3
  method Main() {
    Test();
  }
}
