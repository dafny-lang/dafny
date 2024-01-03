
include "/Users/rwillems/SourceCode/dafny2/Source/DafnyStandardLibraries/src/DafnyStdLibs/MutableCollections/MutableCollections.dfy"

module Example {
  import opened DafnyStdLibs.MutableCollections

  method {:test} TraverseKeysWithoutInterruption() {
    var m := new MutableMap<int, int>();
    m.Put(3, 2);
    m.Put(4, 1);
    
    var s: set<int> := {};
    var keyIterator := m.Keys();
    var hasNext := keyIterator.MoveNext();
    while(hasNext)
      decreases hasNext, |keyIterator.remainingElements|
      invariant !keyIterator.WasInterrupted()
      invariant keyIterator.current.Some? ==> { keyIterator.current.Extract() } + s + keyIterator.remainingElements == m.content().Keys
      invariant keyIterator.current.None? ==> s + keyIterator.remainingElements == m.content().Keys
      invariant keyIterator.current.None? ==> keyIterator.remainingElements == {}
        
      // Surprised I need this. I thought Dafny would figure that this would does not need a modified clause
      invariant {3,4} == m.content().Keys
    {
      var currentKey := keyIterator.Current();
      s := s + {currentKey};
      hasNext := keyIterator.MoveNext();
    }
        
    assert s == {3, 4};
  }

  method {:test} TraverseKeysWithInterruption() {
    var m := new MutableMap<int, int>();
    m.Put(3, 2);
    m.Put(4, 1);
    
    var s: set<int> := {};
    var keyIterator := m.Keys();
    m.Put(5, 0);
    var hasNext := keyIterator.MoveNext();
    while(hasNext)
      decreases hasNext, |keyIterator.remainingElements|
      invariant s == {}
    {
      var currentKey := keyIterator.Current();
      s := s + {currentKey};
      hasNext := keyIterator.MoveNext();
    }
    
    assert s == {};
  }
}