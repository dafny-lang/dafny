include "/Users/rwillems/SourceCode/dafny2/Source/DafnyStandardLibraries/src/DafnyStdLibs/Wrappers.dfy"
 
module {:extern "System.Collections.Generic"} DafnyStdLibs.MutableCollections.CSharp {
  import opened Wrappers
  // import opened MutableCollections

  // With a {:property} attribute this wrapper becomes obsolete
  function {:extern} DictionaryLength<K(==),V(==)>(dic: Dictionary<K,V>): (r: nat)
    ensures r == |dic.content|

  // With a {:indexer} attribute this wrapper becomes obsolete
  method {:extern} DictionarySet<K(==),V(==)>(dic: Dictionary<K,V>, k: K, v: V)
    modifies dic
    ensures k in dic.content.Keys && v == dic.content[k]
    ensures k in old(dic.content).Keys ==> dic.content.Values + {old(dic.content)[k]} == old(dic.content).Values + {v}
    ensures k !in old(dic.content).Keys ==> dic.content.Values == old(dic.content).Values + {v} 

  // With a {:indexer} attribute this wrapper becomes obsolete
  function {:extern} DictionaryGet<K(==),V(==)>(dic: Dictionary<K,V>, k: K): (value: V)
    reads dic
    requires k in dic.content.Keys
    ensures value == dic.content[k]

  class {:extern "Dictionary" } Dictionary<K(==),V(==)> 
  {
    ghost var content: map<K, V> 

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