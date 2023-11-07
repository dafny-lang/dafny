include "/Users/rwillems/SourceCode/dafny2/Source/DafnyStandardLibraries/src/DafnyStdLibs/Wrappers.dfy"
include "/Users/rwillems/SourceCode/dafny2/Source/DafnyStandardLibraries/src/DafnyStdLibs/BoundedInts.dfy"

module {:extern "java.lang"} JavaLang {
  class {:extern "Object"} Object {

  }
}
module {:extern "java.util"} DafnyStdLibs.Java {
  import opened Wrappers
  import opened JavaLang
  import opened BoundedInts

  // import opened MutableCollections

  class {:extern "HashMap" } HashMap<K(==),V(==)> 
  {
    ghost var content: map<K, V> 

    function {:extern "get" } Get(k: K): (r: V)
      reads this
      requires k in content.Keys
      ensures r == content[k]

    method {:extern "put" } Put(k: K, v: V)
      modifies this
      ensures k in content.Keys && v == content[k]
      ensures k in old(content).Keys ==> content.Values + {old(content)[k]} == old(content).Values + {v}
      ensures k !in old(content).Keys ==> content.Values == old(content).Values + {v} 

    function {:extern "containsKey" } ContainsKey(key: K /* Object */): (r: bool)
      reads this
      ensures r <==> key in this.content.Keys

    method {:extern "remove" } Remove(k: K /* Object */)
      modifies this
      ensures this.content == old(this.content) - {k}
      ensures k in old(this.content).Keys ==> this.content.Values + {old(this.content)[k]} == old(this.content).Values

    function {:extern "size" } Size(): (r: int32)
      ensures (r as int) == |this.content.Keys|
      
    constructor {:extern} () 
      ensures this.content == map[]
  }
}