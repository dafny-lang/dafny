
include "separatedclass.dfy"
include "concurrentlinkedlist.dfy"

module ConcurrentHashMap {

  import opened ConcurrentDoublyLinkedList
  import opened SeparatedClasses

  datatype Option<T> = Some(value: T) | None

  type KeyValuePair<K, V> = (K, V)

  class ConcurrentHashMap<K(==), V> extends OwnedObject {

    ghost const inv: KeyValuePair<K, V> -> bool

    var table: HashTable<K, V>

    ghost predicate Valid() 
      reads this, table
    {
      && table.Owner != this
      && (IgnoreFraming(table); table.Valid())
      && inv == table.inv
    }

    constructor(ghost inv: KeyValuePair<K, V> -> bool)
      ensures this.inv == inv
      ensures forall bucket <- table.storage.a[..] :: bucket == null
      ensures Valid()
    {
      this.inv := inv;
      table := new HashTable(inv);
    }

    method Get(k: K) returns (v: Option<V>)
      requires Valid()
    {
      // IgnoreFraming(table);
      var bucket := table.GetBucket(k);
      var node := bucket.FindBy((pair: (K, V)) => pair.0 == k);
      v := if node == null then None else Some(node.value.1);
    }

    // TODO: How to express that multiple Puts should not interfere with each other?
    // i.e. that simultaneous puts of two different keys should never cause one of the keys to not be added.
    // This is different from a simultaneous Put and Remove of the same key.
    method {:vcs_split_on_every_assert} Put(k: K, v: V)
      requires Valid()
      requires inv((k, v))
      // TODO: Shouldn't be necessary
      modifies table.Repr
      modifies set bucket, o | bucket in table.storage.a[..] && bucket != null && o in bucket.Items :: o
    {
      // TODO: Define a maximum table size, and prove that if we have obstruction
      // then the table size must have grown, and therefore our loop
      // decreases MAX_TABLE_SIZE - table.storage.a.Length.
      // This is less dangerous than only retrying a certain number
      // of times around the loop.
      // Ideally we would have a way of proving that
      // if CheckBucket() failed, the table MUST have increases in size.
      while (true) 
        invariant Valid()
      {
        var bucket := table.GetBucket(k);
        assert table.Valid();
        
        bucket.Push((k, v));

        // Necessary in case a resizing happened while we were busy pushing into the bucket
        var success := table.CheckBucket(k, bucket);
        if success {
          return;
        }
      }
    }

    // TODO: will be similar to Put above, including needing to check
    // the bucket hasn't been replaced by a resize
    method Remove(k: K) returns (wasPresent: bool)

  }

  function Hash<T>(t: T): nat

  class {:separated} HashTable<K, V> extends OwnedObject {

    ghost const inv: ((K, V)) -> bool

    var storage: OwnedArray<ConcurrentDoublyLinkedList?<(K, V)>>

    ghost var Value: map<K, V>
    ghost var {:separatedHeap} Repr: set<OwnedObject>

    ghost predicate Valid() 
      reads this, Repr
    {
      && this in Repr
      && Owner == this
      && storage in Repr
      && 0 < storage.a.Length
      && forall r <- Repr :: r.Owner == this
      // TODO: Express the hashcode invariant as well?
      && forall t <- storage.a[..] | t != null :: t.Invariant() && t.inv == inv
      // TODO: Not actually expressable with separated classes :(
      && MapValue(storage.a[..]) == Value
    }

    ghost function MapValue(buckets: seq<ConcurrentDoublyLinkedList?<(K, V)>>): map<K, V> 
      reads buckets
      reads set bucket <- buckets, o <- (if bucket == null then [] else bucket.Items) :: o
    {
      if |buckets| == 0 || buckets[0] == null then
        map[]
      else
        BucketMapValue(buckets[0].Items) + MapValue(buckets[1..])
    }

    ghost function BucketMapValue(items: seq<LinkedListNode<(K, V)>>): map<K, V> 
      reads items
    {
      if |items| == 0 then
        map[]
      else
        var pair := items[0].value;
        map[pair.0 := pair.1] + BucketMapValue(items[1..])
    }

    constructor(ghost inv: KeyValuePair<K, V> -> bool) 
      ensures Valid()
      ensures this.inv == inv
      ensures forall bucket <- storage.a[..] :: bucket == null
    {
      Owner := this;

      var a := new ConcurrentDoublyLinkedList?<(K, V)>[8](i => null);
      storage := new OwnedArray(a);
      
      this.inv := inv;
      Value := map[];
      Repr := {this, storage};
    }

    method GetBucket(key: K) returns (bucket: ConcurrentDoublyLinkedList<(K, V)>)
      requires Valid()
      modifies this, storage.a
      ensures Valid()
      ensures bucket in storage.a[..]
      ensures bucket.Invariant() && bucket.inv == inv
    {
      var hashcode := Hash(key);
      var bucketIndex := hashcode % storage.a.Length;
      // TODO: This part limits concurrent reads a fair bit
      // since then we need a modify lock at runtime.
      if storage.a[bucketIndex] == null {
        storage.a[bucketIndex] := new ConcurrentDoublyLinkedList(inv);
      }
      return storage.a[bucketIndex];
    }

    method CheckBucket(key: K, bucket: ConcurrentDoublyLinkedList<(K, V)>) returns (same: bool) 
      requires Valid()
    {
      var hashcode := Hash(key);
      var bucketIndex := hashcode % storage.a.Length;
      return storage.a[bucketIndex] == bucket;
    }

    method Resize()
      requires Valid()
      // TODO: accidentally got away with not writing Repr here,
      // but Valid() ==> this in Repr, so that should be legal still?
      modifies this
      ensures Valid()
      ensures fresh(Repr - old(Repr))
      ensures old(storage.a.Length) <= storage.a.Length
      ensures storage.a.Length == old(storage.a.Length) * 2
      // TODO: Should ensure that the set of nodes is still the same!
    {
      var newLength := storage.a.Length * 2;
      var newStorage := new ConcurrentDoublyLinkedList?<(K, V)>[newLength](i => null);
      
      // TODO: Actually split each bucket into the two new buckets
      // See ConcurrentDoublyLinkedList.SplitBy

      storage := new OwnedArray(newStorage);
      Repr := {this, storage};
    }
  }
}
