
include "/Users/rwillems/SourceCode/dafny2/Source/DafnyStandardLibraries/src/DafnyStdLibs/MutableCollections/MutableCollections.dfy"

module Example {
  import opened DafnyStdLibs.MutableCollections

  method {:test} TraverseKeysWithoutInterruption() {
    var m := new MutableMap<int, int>();
    m.Put(3, 2);
    m.Put(4, 1);
    
    var s: set<int> := {};
    var keyIterator := m.Keys();
    var currentKey := keyIterator.Next();
    while(currentKey.Some?)
      decreases !currentKey.IsFailure(), |keyIterator.remainingElements|
      invariant !keyIterator.WasInterrupted()
      invariant currentKey.Some? ==> { currentKey.Extract() } + s + keyIterator.remainingElements == m.content().Keys
      invariant currentKey.None? ==> s + keyIterator.remainingElements == m.content().Keys
      invariant currentKey.None? ==> keyIterator.remainingElements == {}
        
      // Surprised I need this. I thought Dafny would figure that this would does not need a modified clause
      invariant {3,4} == m.content().Keys
    {
      s := s + {currentKey.Extract()};
      currentKey := keyIterator.Next();
    }
        
    assert s == {3, 4};
  }

  method {:test} TraverseKeysWithInterruption() {
    var m := new MutableMap<int, int>();
    m.Put(3, 2);
    m.Put(4, 1);
    
    var s: set<int> := {};
    var keyIterator := m.Keys();
    m.Put(5,0);
    var currentKey := keyIterator.Next();
    while(currentKey.Some?)
      decreases !currentKey.IsFailure(), |keyIterator.remainingElements|
      invariant s == {}
    {
      s := s + {currentKey.Extract()};
      currentKey := keyIterator.Next();
      assert currentKey.None?;
    }
    
    assert s == {};
  }
}