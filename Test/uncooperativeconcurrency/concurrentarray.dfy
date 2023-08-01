

// Concurrent array that resizes on demand.
// Essentially like a caching map from nat -> T
class {:separated} ConcurrentArray<T> {

    ghost const inv: T -> bool

    // TODO: This may need to be more like an Action<(), T> to
    // create the value if T is a reference type.
    // But it might be better to just use T? with null in that case instead.
    const default: T
    var storage: array<T>

    ghost var {:separatedHeap} Repr: set<object>

    ghost predicate Valid() 
      reads this, Repr
    {
      && this in Repr
      && storage in Repr
      && inv(default)
      && forall t <- storage[..] :: inv(t)
      // && forall v <- Items :: v.Owner == this
    }

    constructor(default: T, ghost inv: T -> bool) 
      requires inv(default)
    {
      this.default := default;
      this.storage := new T[10](i => default);
    }

    function Select(i: nat): (r: T)
      requires Valid()
      reads this, Repr
      ensures inv(r)
    {
      if i < storage.Length then
        storage[i]
      else
        default
    }

    method Update(i: nat, newValue: T) 
      requires Valid()
      modifies Repr
    {
      if storage.Length <= i {
        Resize(i + 1);
      }
      assert i < storage.Length;
      storage[i] := newValue;
    }

    method Resize(newCapacity: int)
      requires Valid()
      // TODO: accidentally got away with not writing Repr here,
      // but Valid() ==> this in Repr, so that should be legal still?
      modifies this
      ensures Valid()
      ensures fresh(Repr - old(Repr))
      ensures old(storage.Length) <= storage.Length
      ensures newCapacity <= storage.Length
    {
      if newCapacity <= storage.Length {
        return;
      }
      var newStorage := new T[newCapacity](i => default);
      // Ideally this could be compiled to an optimized array copy
      // (e.g. System.arraycopy in Java)
      forall i | 0 <= i < storage.Length {
        newStorage[i] := storage[i];
      }
      storage := newStorage;
      Repr := {this, storage};
    }
  }