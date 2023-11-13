include "/Users/rwillems/SourceCode/dafny2/Source/DafnyStandardLibraries/src/DafnyStdLibs/Wrappers.dfy"

module {:extern "MutableCollections"} DafnyStdLibs.MutableCollections {
  import opened Wrappers
  // import opened MutableCollections

  // TODO: let this replace MutableCollections.MutableMap
  class {:extern} HashMap<K(==),V(==)> {
       
    constructor {:extern} ()
      ensures this.content() == map[]
  
    ghost function {:axiom} content(): map<K, V> reads this
  
    method {:extern} Put(k: K, v: V)
      modifies this
      ensures this.content() == old(this.content())[k := v]
      ensures k in old(this.content()).Keys ==> this.content().Values + {old(this.content())[k]} == old(this.content()).Values + {v}
      ensures k !in old(this.content()).Keys ==> this.content().Values == old(this.content()).Values + {v}
  
    predicate {:extern} HasKey(k: K)
      reads this
      ensures HasKey(k) <==> k in this.content().Keys
      
    function {:extern} Select(k: K): (v: V)
      reads this
      requires this.HasKey(k)
      ensures v in this.content().Values
      ensures this.content()[k] == v
  
    method {:extern} Remove(k: K)
      modifies this
      ensures this.content() == old(this.content()) - {k}
      ensures k in old(this.content()).Keys ==> this.content().Values + {old(this.content())[k]} == old(this.content()).Values
  
    function {:extern} Size(): (size: int)
      reads this
      ensures size == |this.content().Items|
  
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
  }
}