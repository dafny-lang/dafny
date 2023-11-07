// include "/Users/rwillems/SourceCode/dafny2/Source/DafnyStandardLibraries/src/DafnyStdLibs/MutableCollections/MutableCollections.dfy"
include "/Users/rwillems/SourceCode/dafny2/Source/DafnyStandardLibraries/src/DafnyStdLibs/MutableCollections/Java/HashMap.dfy"

module DafnyStdLibs.MutableCollections {
  import opened Wrappers
  // import opened MutableCollections
  import opened Java

  class MutableMap<K(==),V(==)> {
    const data: HashMap<K,V>
       
    constructor ()
      ensures this.content() == map[]
    {
      this.data := new HashMap<K,V>();
    }
  
    ghost function content(): map<K, V> 
     reads data {
      data.content
    }
  
    method Put(k: K, v: V)
      modifies this
      ensures this.content() == old(this.content())[k := v]
      ensures k in old(this.content()).Keys ==> this.content().Values + {old(this.content())[k]} == old(this.content()).Values + {v}
      ensures k !in old(this.content()).Keys ==> this.content().Values == old(this.content()).Values + {v} 
    {
      this.data.Put(k, v);
    }
  
    predicate HasKey(k: K)
      reads this, data
      ensures HasKey(k) <==> k in this.content().Keys 
    {
      data.ContainsKey(k)
    }
      
    function Select(k: K): (v: V)
      reads this
      requires this.HasKey(k)
      ensures v in this.content().Values
      ensures this.content()[k] == v 
    {
      this.data.Get(k)
    }
  
    method Remove(k: K)
      modifies this
      ensures this.content() == old(this.content()) - {k}
      ensures k in old(this.content()).Keys ==> this.content().Values + {old(this.content())[k]} == old(this.content()).Values 
    {
      this.data.Remove(k);
    }
  
    function Size(): (size: int)
      reads this
      ensures size == |this.content().Items| 
    {
      this.data.Size() as int
    }
  
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