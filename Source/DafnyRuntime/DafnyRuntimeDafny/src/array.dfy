
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
  //    I don't think it's a safe assumption that every target language
  //    will optimize a loop over a range of array indices into an
  //    equivalent memory copy, especially since the 
  //    Dafny compilation process is hardly guaranteed to produce
  //    code amenable to such optimizations. :)
  //    See https://github.com/dafny-lang/dafny/issues/2447.
  //
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

    // TODO: Might want a copy that takes a ResizeableArray as well
    method WriteRangeArray(start: nat, other: ImmutableArray<T>)
      requires Valid()
      requires other.Valid()
      requires start <= Length()
      requires start + other.Length() <= Length()
      modifies Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures values == 
        old(values)[..start] + 
        other.CellValues() +
        old(values)[(start + other.Length())..]

    method Freeze(size: nat) returns (ret: ImmutableArray<T>)
      requires Valid()
      requires size <= Length()
      requires forall i | 0 <= i < size :: values[i].Set?
      ensures ret.Valid()
      ensures |ret.values| == size
      ensures forall i | 0 <= i < size :: ret.values[i] == values[i].value
      // Explicitly doesn't ensure Valid()!
  }

  datatype ArrayCell<T> = Set(value: T) | Unset

  trait {:extern} ImmutableArray<T> {

    ghost const values: seq<T>

    ghost predicate Valid()

    ghost function CellValues(): seq<ArrayCell<T>> {
      seq(|values|, i requires 0 <= i < |values| => Set(values[i]))
    }

    function Length(): nat 
      requires Valid()
      ensures Length() == |values|

    function At(index: nat): T 
      requires Valid()
      requires index < |values|
      ensures At(index) == values[index]
  }

  // TODO: More consistent method names.
  // This is internal for now but would be great to have in a shared library.
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
      var values := storage.Freeze(size);
      newStorage.WriteRangeArray(0, values);
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

    method Append(other: ImmutableArray<T>) 
      requires Valid()
      requires other.Valid()
      modifies Repr
      ensures ValidAndDisjoint()
      ensures Value() == old(Value()) + other.values
    {
      if storage.Length() < size + other.Length() {
        Reallocate(Math.Max(size + other.Length(), storage.Length() * 2));
      }
      storage.WriteRangeArray(size, other);
      size := size + other.Length();
    }

    method Freeze() returns (ret: ImmutableArray<T>)
      requires Valid()
      ensures ret.Valid()
      ensures ret.values == Value()
      // Explicitly doesn't ensure Valid()!
    {
      ret := storage.Freeze(size);
    }
  }

  ///
  // Feasibility implementation
  ///

  class DafnyArray<T> extends Array<T> {
    const valuesArray: array<ArrayCell<T>>

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

    method WriteRangeArray(start: nat, other: ImmutableArray<T>)
      requires Valid()
      requires other.Valid()
      requires start <= Length()
      requires start + other.Length() <= Length()
      modifies Repr
      ensures Valid()
      ensures Repr == old(Repr)
      ensures values == 
        old(values)[..start] + 
        other.CellValues() +
        old(values)[(start + other.Length())..]
    {
      forall i | 0 <= i < other.Length() {
        valuesArray[start + i] := Set(other.At(i));
      }
      values := valuesArray[..];
    }

    method Freeze(size: nat) returns (ret: ImmutableArray<T>)
      requires Valid()
      requires size <= Length()
      requires forall i | 0 <= i < size :: values[i].Set?
      ensures ret.Valid()
      ensures |ret.values| == size
      ensures forall i | 0 <= i < size :: ret.values[i] == values[i].value
    {
      ret := new DafnyImmutableArray(this, size);
    }
  }

  class DafnyImmutableArray<T> extends ImmutableArray<T> {

    const valuesSeq: seq<T>

    ghost predicate Valid() {
      values == valuesSeq
    }

    constructor(a: Array<T>, size: nat)
      requires a.Valid()
      requires size <= a.Length()
      requires forall i | 0 <= i < size :: a.values[i].Set?
      ensures Valid()
      ensures |values| == size
      ensures forall i | 0 <= i < size :: values[i] == a.values[i].value
    {
      var valuesSeq := ValuesFromArray(a, size);
      this.values := valuesSeq;
      this.valuesSeq := valuesSeq;
    }

    static function ValuesFromArray(a: Array<T>, size: nat): (ret: seq<T>)
      requires a.Valid()
      requires size <= a.Length()
      requires forall i | 0 <= i < size :: a.values[i].Set?
      reads a, a.Repr
      ensures |ret| == size
      ensures forall i | 0 <= i < size :: ret[i] == a.values[i].value
    {
      if size == 0 then
        []
      else
        ValuesFromArray(a, size - 1) + [a.Read(size - 1)]
    }

    function Length(): nat 
      requires Valid()
      ensures Length() == |values|
    {
      |valuesSeq|
    }

    function At(index: nat): T
      requires Valid()
      requires index < |values|
      ensures At(index) == values[index]
    {
      valuesSeq[index]
    }
  }
}