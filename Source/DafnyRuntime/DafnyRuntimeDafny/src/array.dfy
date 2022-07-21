
// TODO: Avoid depending on stdlib
include "../../../../Test/libraries/src/Math.dfy"

include "frames.dfy"

module {:options "/functionSyntax:4"} Arrays {

  import opened Frames
  import opened Math

  //
  // We use this instead of the built-in Dafny array<T> type for two reasons:
  // 
  // 1. Every element of an array<T> must be initialized.
  //    This means you have to provide initial values when creating one,
  //    which you can't do in generic code if your T is not auto-initializable (T(0)).
  //    This RFC proposes a way to model uninitialized storage
  //    that could be compiled to efficient enough code instead
  //    (i.e. the Unset constructor below could be marked ghost):
  //    https://github.com/dafny-lang/rfcs/pull/11
  //
  // 2. The array<T> type does not support any bulk-assignment
  //    operations, which are important to optimize as much as possible
  //    in this performance-sensitive code.
  //    See https://github.com/dafny-lang/dafny/issues/2447.
  //
  datatype ArrayCell<T> = Set(value: T) | Unset

  trait {:extern} Array<T> extends Validatable {

    ghost var values: seq<ArrayCell<T>>

    function Length(): nat
      requires Valid()
      reads Repr
      ensures Length() == |values|

    function Read(i: nat): (ret: T)
      requires Valid()
      requires i < Length()
      requires values[i].Set?
      reads this, Repr
      ensures ret == values[i].value

    method Write(i: nat, t: T)
      requires Valid()
      requires i < Length()
      modifies Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures values == old(values)[..i] + [Set(t)] + old(values)[(i + 1)..]
      ensures Read(i) == t

    method WriteRange(start: nat, from: seq<T>)
      requires Valid()
      requires start <= Length()
      requires start + |from| <= Length()
      modifies Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures values == 
        old(values)[..start] + 
        seq(|from|, i requires 0 <= i < |from| => Set(from[i])) + 
        old(values)[(start + |from|)..]

    method WriteRangeArray(start: nat, from: Array<T>, fromStart: nat, fromEnd: nat)
      requires Valid()
      requires from.Valid()
      requires start <= Length()
      requires fromStart <= fromEnd <= from.Length()
      requires start + (fromEnd - fromStart) <= Length()
      requires forall i | fromStart <= i < fromEnd :: from.values[i].Set?
      requires Repr !! from.Repr
      modifies Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures values == 
        old(values)[..start] + 
        from.values[fromStart..fromEnd] + 
        old(values)[(start + (fromEnd - fromStart))..]
  }

  // Feasibility implementation
  class DafnyArray<T> extends Array<T> {
    var valuesArray: array<ArrayCell<T>>

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      && Repr == {this, valuesArray}
      && valuesArray[..] == values
    }

    constructor(length: nat) 
      ensures Valid()
      ensures fresh(Repr)
      ensures values == seq(length, i => Unset)
    {
      valuesArray := new ArrayCell<T>[length](i => Unset);
      new;
      values := valuesArray[..];
      Repr := {this, valuesArray};
    }

    function Length(): nat
      requires Valid()
      reads Repr
      ensures Length() == |values|
    {
      valuesArray.Length
    }

    function Read(i: nat): (ret: T)
      requires Valid()
      requires i < Length()
      requires values[i].Set?
      reads this, Repr
      ensures ret == values[i].value
    {
      valuesArray[i].value
    }

    method Write(i: nat, t: T)
      requires Valid()
      requires i < Length()
      modifies Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures Length() == old(Length())
      ensures values == old(values)[..i] + [Set(t)] + old(values)[(i + 1)..]
      ensures Read(i) == t
    {
      valuesArray[i] := Set(t);

      values := valuesArray[..];
    }

    method WriteRange(start: nat, from: seq<T>)
      requires Valid()
      requires start <= Length()
      requires start + |from| <= Length()
      modifies Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures values == 
        old(values)[..start] + 
        seq(|from|, i requires 0 <= i < |from| => Set(from[i])) + 
        old(values)[(start + |from|)..]
    {
      forall i | 0 <= i < |from| {
        valuesArray[start + i] := Set(from[i]);
      }
      values := valuesArray[..];
    }

    method WriteRangeArray(start: nat, from: Array<T>, fromStart: nat, fromEnd: nat)
      requires Valid()
      requires from.Valid()
      requires start <= Length()
      requires fromStart <= fromEnd <= from.Length()
      requires start + (fromEnd - fromStart) <= Length()
      requires forall i | fromStart <= i < fromEnd :: from.values[i].Set?
      requires Repr !! from.Repr
      modifies Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures values == 
        old(values)[..start] + 
        from.values[fromStart..fromEnd] + 
        old(values)[(start + (fromEnd - fromStart))..]
    {
      var n := fromEnd - fromStart;
      forall i | 0 <= i < n {
        valuesArray[start + i] := Set(from.Read(fromStart + i));
      }
      values := valuesArray[..];
    }
  }

  // TODO: More consistent method names.
  // This is internal for now but would be great to have in a shared library
  class ResizableArray<T> extends Validatable {
    var storage: Array<T>
    var size: nat

    const MIN_SIZE := 10;

    ghost predicate Valid() reads this, Repr 
      ensures Valid() ==> this in Repr
    {
      && this in Repr
      && ValidComponent(storage)
      && 0 <= size <= storage.Length()
      && forall i | 0 <= i < size :: storage.values[i].Set?
    }

    constructor(length: nat) 
      ensures Valid()
      ensures Value() == []
      ensures fresh(Repr)
    {
      // TODO: Replace with extern to create native array
      storage := new DafnyArray<T>(length);
      size := 0;
      new;
      Repr := {this} + storage.Repr;
    }

    ghost function Value(): seq<T>
      requires Valid()
      reads this, Repr
    {
      seq(size, i requires 0 <= i < size && Valid() reads this, Repr => storage.Read(i))
    }

    function At(index: nat): T 
      requires Valid()
      requires index < size
      reads this, Repr
      ensures At(index) == Value()[index]
    {
      storage.Read(index)
    }

    function Last(): T 
      requires Valid()
      requires 0 < size
      reads this, Repr
      ensures Last() == Value()[size - 1]
    {
      storage.Read(size - 1)
    }

    method AddLast(t: T) 
      requires Valid()
      modifies Repr
      ensures ValidAndDisjoint()
      ensures Value() == old(Value()) + [t]
    {
      if size == storage.Length() {
        Reallocate(Math.Max(MIN_SIZE, storage.Length() * 2));
      }
      storage.Write(size, t);
      size := size + 1;
    }

    method Reallocate(newCapacity: nat) 
      requires Valid()
      requires size <= newCapacity
      modifies Repr
      ensures ValidAndDisjoint()
      ensures storage.Length() == newCapacity
      ensures Value() == old(Value())
    {
      var newStorage := new DafnyArray<T>(newCapacity);
      newStorage.WriteRangeArray(0, storage, 0, size);
      storage := newStorage;

      Repr := {this} + storage.Repr;
    }

    method RemoveLast() returns (t: T) 
      requires Valid()
      requires 0 < size
      modifies Repr
      ensures ValidAndDisjoint()
      ensures old(Value()) == Value() + [t]
      ensures Value() == old(Value()[..(size - 1)])
      ensures t in old(Value())
    {
      t := storage.Read(size - 1);
      size := size - 1;
    }

    method Append(other: ResizableArray<T>) 
      requires Valid()
      requires other.Valid()
      requires Repr !! other.Repr
      modifies Repr
      ensures ValidAndDisjoint()
      ensures Value() == old(Value()) + other.Value()
    {
      if storage.Length() < size + other.size {
        Reallocate(Math.Max(size + other.size, storage.Length() * 2));
      }
      storage.WriteRangeArray(size, other.storage, 0, other.size);
      size := size + other.size;
    }
  }
}