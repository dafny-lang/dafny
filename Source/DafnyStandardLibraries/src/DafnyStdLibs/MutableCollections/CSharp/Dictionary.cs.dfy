include "/Users/rwillems/SourceCode/dafny2/Source/DafnyStandardLibraries/src/DafnyStdLibs/Wrappers.dfy"
 
module DafnyStdLibs.CSharp.System.Collections.Generic {
  import opened Wrappers
  import opened MutableCollections

  trait Exception {

  }
  trait IEnumerator<T> {
    ghost const version: nat
    ghost const source: MutableIteratorSource
    ghost var remainingElements: set<T>
    ghost var wasInterrupted: bool
    ghost var currentIsDefined: bool
    ghost var current: T
    
    method {:extern} {:wrapException} MoveNext() returns (r: Result<bool, Exception>)
      ensures (version != source.version()) == wasInterrupted
      ensures wasInterrupted == r.Success?
      ensures if (!wasInterrupted && |remainingElements| > 0) 
        then currentIsDefined && { current } + remainingElements == old(remainingElements) && 1 + |remainingElements| == |old(remainingElements)|
        else !currentIsDefined && old(remainingElements) == remainingElements

    function {:extern} {:property} Current(): (v: T)
      reads this
      requires currentIsDefined
      ensures v == current
  }

  trait IEnumerable {
    ghost var version: nat
  }

  class {:extern "System.Collections.Generic", "Dictionary" } Dictionary<K(==),V(==)> 
    extends IEnumerable
  {
    ghost var content: map<K, V> 

    // Need a C# specific property to specify that I want to use the property indexer Dictionary[K key]
    function {:extern} {:indexer} IndexGetter(k: K): (value: V)
      reads this
      requires k in content.Keys
      ensures value == content[k]

    method {:extern} {:indexer} IndexSetter(k: K, v: V)
      reads this
      modifies this
      ensures this.version == old(this.version) + 1 
      ensures k in content.Keys && v == content[k]
      ensures k in old(this.content).Keys ==> this.content.Values + {old(this.content)[k]} == old(this.content).Values + {v}
      ensures k !in old(this.content).Keys ==> this.content.Values == old(this.content).Values + {v} 

    method {:extern} Add(k: K, v: V)
      modifies this
      ensures this.version == old(this.version) + 1 
      requires !(k in this.content.Keys) // Prevent the exception
      ensures this.version == old(this.version) + 1 
      ensures this.content == old(this.content)[k := v]
      ensures k !in old(this.content).Keys ==> this.content.Values == old(this.content).Values + {v} 

    function {:extern} ContainsKey(key: K): (r: bool)
      reads this
      ensures r <==> key in this.content.Keys

    method {:extern} Remove(k: K)
      modifies this
      ensures this.content == old(this.content) - {k}
      ensures this.version == old(this.version) + 1 
      ensures k in old(this.content).Keys ==> this.content.Values + {old(this.content)[k]} == old(this.content).Values

    function {:extern} {:property} Length(): (r: nat)
      ensures r == |this.content.Keys|
      
    constructor {:extern} () 
      ensures this.content == map[]
      ensures version == 0
  }
}