
include "/Users/rwillems/SourceCode/dafny2/Source/DafnyStandardLibraries/src/DafnyStdLibs/MutableCollections/MutableCollections.dfy"

module Example {
  import opened DafnyStdLibs.MutableCollections

  method {:test} TraverseKeysWithoutInterruption() {
    var m := new MutableMap<int, int>();
    m.Put(3, 2);
    m.Put(4, 1);
    assert {3,4} == m.content().Keys;
    
    var s: set<int> := {};
    var keyIterator := m.Keys();
    assert keyIterator.remainingElements == m.content().Keys;
    var currentKey := keyIterator.Next();
    assert m.version == 2; 
    assert currentKey.None? || currentKey.Extract() in m.content().Keys;
    assert currentKey.Some? ==> { currentKey.Extract() } + s + keyIterator.remainingElements == m.content().Keys;
    assert {3,4} == m.content().Keys;
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
      assert currentKey.None? || currentKey.Extract() in m.content().Keys;
    }
    
    assert keyIterator.remainingElements == {};
    assert s + keyIterator.remainingElements == m.content().Keys;
        
    assert s == m.content().Keys;
    assert {3,4} == m.content().Keys;
    assert s == {3, 4};
  }

  method {:test} TraverseKeysWithInterruption() {
    var m := new MutableMap<int, int>();
    m.Put(3, 2);
    m.Put(4, 1);
    assert {3,4} == m.content().Keys;
    
    var s: set<int> := {};
    var keyIterator := m.Keys();
    assert keyIterator.remainingElements == {3 , 4};
    assert m.version == keyIterator.version;
    m.Put(5,0);
    assert m.version != keyIterator.version;
    var currentKey := keyIterator.Next();
    assert (keyIterator.version != keyIterator.source.version) == keyIterator.wasInterrupted;
    assert (keyIterator.version != m.version) == keyIterator.wasInterrupted;
    assert m.version != keyIterator.version;
    assert keyIterator.wasInterrupted;
    assert currentKey.None?;
    // why does this not assert?
    assume keyIterator.remainingElements == {3 , 4};
    while(currentKey.Some?)
      decreases !currentKey.IsFailure(), |keyIterator.remainingElements|
      invariant s == {}
      invariant keyIterator.remainingElements == {3 , 4}
      // Surprised I need this. I thought Dafny would figure that this would does not need a modified clause
      invariant {5, 3, 4} == m.content().Keys
    {
      s := s + {currentKey.Extract()};
      currentKey := keyIterator.Next();
      assert currentKey.None?;
    }
    
    assert keyIterator.remainingElements == {3 , 4};
    assert s == {};
  }
}