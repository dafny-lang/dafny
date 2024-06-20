include "/Users/rwillems/SourceCode/dafny2/Source/DafnyStandardLibraries/src/DafnyStdLibs/MutableCollections/MutableCollections.dfy"
include "/Users/rwillems/SourceCode/dafny2/Source/DafnyStandardLibraries/src/DafnyStdLibs/MutableCollections/CSharp/Dictionary.cs.dfy"

module DafnyStdLibs.MutableCollectionsCs {
  import opened Wrappers
  import opened MutableCollections
  import opened CSharp.System.Collections.Generic
  
  class MutableIteratorCs<T(==)> extends MutableIterator<T> {
    var data: IEnumerator<T>

    constructor(data: IEnumerator<T>) {
      this.data := data;
      this.wasInterrupted := false;
    }
    
    ghost function source(): MutableIteratorSource reads this {
      data.source
    }
    ghost function version(): nat reads this {
      data.version
    }

    ghost function remainingElements(): set<T> reads this, data {
      data.remainingElements
    }

    ghost function current(): Option<T> reads this, data {
      if data.currentIsDefined 
      then Some(data.current)
      else None
    }
    
    method {:extern} MoveNext() returns (r: bool)
      modifies this
      ensures (version() != source().version()) == wasInterrupted
      ensures current().Some? == r
      ensures if (!wasInterrupted && |remainingElements()| > 0) 
        then r && var value := current().Extract(); { value } + remainingElements() == old(remainingElements()) 
        && 1 + |remainingElements()| == |old(remainingElements())|
        else !r && old(remainingElements) == remainingElements 
    {
       var result := data.MoveNext();
       if (result.IsFailure()) {
        assert version() != source().version();
        r := false;
        wasInterrupted := true;
       } else {
        r := result.Extract();
        wasInterrupted := false;
       }
    }

    function {:extern} Current(): (v: T)
      reads this, data
      requires current().Some?
      ensures v == current().Extract() {
      data.Current()
    }
  }

  class MutableMapCs<K(==),V(==)> extends MutableIteratorSource {
    const data: Dictionary<K,V>
       
    constructor ()
      ensures this.content() == map[]
      ensures version() == 0
    {
      this.data := new Dictionary<K,V>();
    }
  
    ghost function content(): map<K, V> 
     reads data {
      data.content
    }

    ghost function version(): nat 
      reads this, this.data {
      data.version
    }
  
    method {:extern} Put(k: K, v: V)
      modifies this, data
      ensures this.version() > old(this.version())
      ensures this.content() == old(this.content())[k := v]
      ensures k in old(this.content()).Keys ==> this.content().Values + {old(this.content())[k]} == old(this.content()).Values + {v}
      ensures k !in old(this.content()).Keys ==> this.content().Values == old(this.content()).Values + {v} 
    {
      this.data.IndexSetter(k, v);
    }
    
    function {:extern} Keys(): (keys: MutableIterator<K>)
      reads this
      ensures keys.version() == version()
      ensures keys.remainingElements() == content().Keys
      ensures keys.source() == this
  
    function {:extern} Values(): (values: MutableIterator<V>)
      reads this
      ensures values.version() == version()
      ensures values.remainingElements() == content().Values
      ensures values.source() == this
  
    function {:extern} Items(): (items: MutableIterator<(K,V)>)
      reads this
      ensures items.version() == version()
      ensures items.remainingElements() == set k | k in this.content().Keys :: (k, this.content()[k])
      ensures items.source() == this
  
    predicate {:extern} HasKey(k: K)
      reads this, data
      ensures HasKey(k) <==> k in this.content().Keys 
    {
      data.ContainsKey(k)
    }
      
    function {:extern} Select(k: K): (v: V)
      reads this
      requires this.HasKey(k)
      ensures v in this.content().Values
      ensures this.content()[k] == v 
    {
      this.data.IndexGetter(k)
    }
  
    method {:extern} Remove(k: K)
      modifies this
      ensures this.content() == old(this.content()) - {k}
      ensures k in old(this.content()).Keys ==> this.content().Values + {old(this.content())[k]} == old(this.content()).Values 
    {
      this.data.Remove(k);
    }
  
    function {:extern} Size(): (size: int)
      reads this
      ensures size == |this.content().Items| 
    {
      this.data.Length()
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