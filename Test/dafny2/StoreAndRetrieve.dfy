ghost module A {
  import L = Library;
  class {:autocontracts} StoreAndRetrieve<Thing> {
    ghost var Contents: set<Thing>;
    predicate Valid
    {
      true
    }
    constructor Init()
    {
      Contents := {};
    }
    method Store(t: Thing)
    {
      Contents := Contents + {t};
    }
    method Retrieve(matchCriterion: L.Function) returns (thing: Thing)
      requires exists t :: t in Contents && L.Function.Apply(matchCriterion, t);
      ensures Contents == old(Contents);
      ensures thing in Contents && L.Function.Apply(matchCriterion, thing);
    {
      var k :| k in Contents && L.Function.Apply(matchCriterion, k);
      thing := k;
    }
  }
}

module B refines A {
  class StoreAndRetrieve<Thing> {
    var arr: seq<Thing>;
    predicate Valid
    {
      Contents == set x | x in arr
    }
    constructor Init()
    {
      arr := [];
    }
    method Store...
    {
      arr := arr + [t];
    }
    method Retrieve...
    {
      var i := 0;
      while (i < |arr|)
        invariant i < |arr|;
        invariant forall j :: 0 <= j < i ==> !L.Function.Apply(matchCriterion, arr[j]);
      {
        if (L.Function.Apply(matchCriterion, arr[i])) { break; }
        i := i + 1;
      }
      var k := arr[i];
      ...;
      var a :| Contents == set x | x in a;
      arr := a;
    }
  }
}

module C refines B {
  class StoreAndRetrieve<Thing> {
    method Retrieve...
    {
      ...;
      var a := [thing] + arr[..i] + arr[i+1..];  // LRU behavior
    }
  }
}

module Library {
  // This class simulates function parameters
  class Function {
    static function method Apply<T>(f: Function, t: T): bool
  }
}
