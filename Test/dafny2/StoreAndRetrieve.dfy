// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

// This file shows an example program that uses both refinement and :autocontracts
// specify a class that stores a set of things that can be retrieved using a query.
//
// (For another example that uses these features, see Test/dafny3/CachedContainer.dfy.)

abstract module AbstractInterface {
  class {:autocontracts} StoreAndRetrieve<Thing(==)> {
    ghost var Contents: set<Thing>
    predicate Valid() {
      Valid'()
    }
    predicate {:autocontracts false} Valid'()
      reads this, Repr
    constructor Init()
      ensures Contents == {}
    method Store(t: Thing)
      ensures Contents == old(Contents) + {t}
    method Retrieve(matchCriterion: Thing -> bool) returns (thing: Thing)
      requires exists t :: t in Contents && matchCriterion(t)
      ensures Contents == old(Contents)
      ensures thing in Contents && matchCriterion(thing)
  }
}

abstract module A refines AbstractInterface {
  class StoreAndRetrieve<Thing(==)> ... {
    constructor Init...
    {
      Contents := {};
      Repr := {this};
      new;
      assume Valid'();  // to be checked in module B
    }
    method Store...
    {
      Contents := Contents + {t};
      assume Valid'();  // to be checked in module B
    }
    method Retrieve...
    {
      var k :| assume k in Contents && matchCriterion(k);
      thing := k;
    }
  }
}

abstract module B refines A {
  class StoreAndRetrieve<Thing(==)> ... {
    var arr: seq<Thing>
    predicate Valid'...
    {
      Contents == set x | x in arr
    }
    constructor Init...
    {
      arr := [];
      new;
      assert ...;
    }
    method Store...
    {
      arr := arr + [t];
      ...;
      assert ...;
    }
    method Retrieve...
    {
      var i := 0;
      while (i < |arr|)
        invariant i < |arr|;
        invariant forall j :: 0 <= j < i ==> !matchCriterion(arr[j]);
      {
        if matchCriterion(arr[i]) {
          break;
        }
        i := i + 1;
      }
      var k := arr[i];
      ...;
      var a: seq<Thing> :| assume Contents == set x | x in a;
      arr := a;
    }
  }
}

module C refines B {
  class StoreAndRetrieve<Thing(==)> ... {
    method Retrieve...
    {
      ...;
      var a := [thing] + arr[..i] + arr[i+1..];  // LRU behavior
    }
  }
}

abstract module AbstractClient {
  import S : AbstractInterface

  method Test() {
    var s := new S.StoreAndRetrieve<real>.Init();
    s.Store(20.3);
    var fn := r => true;
    var r := s.Retrieve(fn);
    print r, "\n";  // 20.3
  }
}

module Client refines AbstractClient {
  import S = C
  method Main() {
    Test();
  }
}
