module DafnyStdLibs.MutableCollections {
  import opened DafnyStdLibs.Wrappers
  
  class {:extern "System.Collections.Generic", "Dictionary" } Dictionary<K,V> {
    method {:extern} Add(key: K, value: V)
    method {:extern} ContainsKey(key: K) returns (b: bool) 
  }
  
  class MutableMap<K(==),V(==)> extends MutableIteratorSource<V> {
    const data: Dictionary<K,V>
    var myVersion: nat
    var myContent: map<K,V>
       
    constructor ()
      ensures this.content() == map[]
      ensures version() == 0 
    {
      this.myVersion := 0;
      this.map = map[];
      this.data := new Dictionary<K,V>();
    }
  
    ghost function {:extern} content(): map<K, V> 
      reads this
  
    method {:extern} Put(k: K, v: V)
      modifies this
      ensures this.content() == old(this.content())[k := v]
      ensures k in old(this.content()).Keys ==> this.content().Values + {old(this.content())[k]} == old(this.content()).Values + {v}
      ensures k !in old(this.content()).Keys ==> this.content().Values == old(this.content()).Values + {v}
  
    function version(): nat 
      reads this { myVersion }
  
    function {:extern} Keys(): (keys: MutableIterator<K>)
      reads this
      ensures keys.remainingElements == content().Keys
      ensures keys.source == this
  
    function {:extern} Values(): (values: MutableIterator<V>)
      reads this
      ensures values.remainingElements == content().Values
      ensures values.source == this
  
    function {:extern} Items(): (items: MutableIterator<(K,V)>)
      reads this
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
    const version: nat
    const source: MutableIteratorSource<T>
    var remainingElements: set<T>
    
    method {:extern} Next() returns (o: Option<T>)
      ensures match o {
        case None => source.version() != version || |remainingElements| == 0
        case Some(value) => remainingElements == { value } + old(remainingElements)
      }
  }
  
  trait MutableIteratorSource<T> {
    function version(): nat
      reads this
  }
}