include "/Users/rwillems/SourceCode/dafny2/Source/DafnyStandardLibraries/src/DafnyStdLibs/Wrappers.dfy"
 
module {:extern "MapExtensions"} DafnyStdLibs.MutableCollections.JavaScript {
  import opened Wrappers
  // import opened MutableCollections

  // With a {:property} attribute this wrapper becomes obsolete
  function {:extern} MapLength<K(==),V(==)>(m: Map<K,V>): (r: nat)
    ensures r == |m.content|

  class {:extern "", "Map"} Map<K(==),V(==)> 
  {
    ghost var content: map<K, V> 

    method {:extern "set"} Set(k: K, v: V)
      modifies this
      ensures k in content.Keys && v == content[k]
      ensures k in old(content).Keys ==> content.Values + {old(content)[k]} == old(content).Values + {v}
      ensures k !in old(content).Keys ==> content.Values == old(content).Values + {v} 

    function {:extern "get"} Get(k: K): (value: V)
      reads this
      requires k in content.Keys
      ensures value == content[k]
    
    function {:extern} ContainsKey(key: K): (r: bool)
      reads this
      ensures r <==> key in this.content.Keys

    method {:extern} Remove(k: K)
      modifies this
      ensures this.content == old(this.content) - {k}
      ensures k in old(this.content).Keys ==> this.content.Values + {old(this.content)[k]} == old(this.content).Values
      
    constructor {:extern} () 
      ensures this.content == map[]
  }
}