include "/Users/rwillems/SourceCode/dafny2/Source/DafnyStandardLibraries/src/DafnyStdLibs/Wrappers.dfy"

module DafnyStdLibs.MutableCollections {
  import opened Wrappers
  
  class {:extern} MutableMap<K(==),V(==)> extends MutableIteratorSource<V> {
     
    constructor {:extern} ()
      ensures this.content() == map[]
      ensures version == 0
  
    ghost function {:extern} content(): map<K, V> 
      reads this
  
    method {:extern} Put(k: K, v: V)
      modifies this
      ensures this.version == old(this.version) + 1 
      ensures this.content() == old(this.content())[k := v]
      ensures k in old(this.content()).Keys ==> this.content().Values + {old(this.content())[k]} == old(this.content()).Values + {v}
      ensures k !in old(this.content()).Keys ==> this.content().Values == old(this.content()).Values + {v}
    
    function {:extern} Keys(): (keys: MutableIterator<K>)
      reads this
      ensures keys.version == version
      ensures keys.remainingElements == content().Keys
      ensures keys.source == this
  
    function {:extern} Values(): (values: MutableIterator<V>)
      reads this
      ensures values.version == version
      ensures values.remainingElements == content().Values
      ensures values.source == this
  
    function {:extern} Items(): (items: MutableIterator<(K,V)>)
      reads this
      ensures items.version == version
      ensures items.remainingElements == set k | k in this.content().Keys :: (k, this.content()[k])
      ensures items.source == this
  
    predicate {:extern} HasKey(k: K)
      reads this
      ensures HasKey(k) <==> k in this.content().Keys
      
    function {:extern} Select(k: K): (v: V)
      reads this
      requires this.HasKey(k)
      ensures v in this.content().Values
      ensures this.content()[k] == v
  
    function SelectOpt(k: K): (o: Option<V>)
      reads this
      ensures o.Some? ==> (this.HasKey(k) && o.value in this.content().Values && this.content()[k] == o.value)
      ensures o.None? ==> !this.HasKey(k)
    {
      if this.HasKey(k) then
        Some(this.Select(k))
      else
        None
    }
  
    method {:extern} Remove(k: K)
      modifies this
      ensures this.content() == old(this.content()) - {k}
      ensures k in old(this.content()).Keys ==> this.content().Values + {old(this.content())[k]} == old(this.content()).Values
  
    function {:extern} Size(): (size: int)
      reads this
      ensures size == |this.content().Items|
  }
  
  
  trait MutableIterator<T(==)> {
    ghost const version: nat
    ghost const source: MutableIteratorSource<T>
    ghost var remainingElements: set<T>
    ghost var wasInterrupted: bool
    
    function {:extern} WasInterrupted(): (r: bool)
     ensures r == wasInterrupted
    
    method {:extern} Next() returns (o: Option<T>)
      ensures (version != source.version) == wasInterrupted
      ensures if (!wasInterrupted && |remainingElements| > 0) 
        then o.Some? && var value := o.Extract(); { value } + remainingElements == old(remainingElements) && 1 + |remainingElements| == |old(remainingElements)|
        else o.None? && old(remainingElements) == remainingElements
    //  ensures match o {
    //   case None => old(remainingElements) == remainingElements && 
    //       (wasInterrupted || |remainingElements| == 0)
    //   case Some(value) => { value } + remainingElements == old(remainingElements) 
    //     && 1 + |remainingElements| == |old(remainingElements)|
    //     && !wasInterrupted
    //  }
  }
  
  trait MutableIteratorSource<T> {
    ghost var version: nat
  }
}