
include "../src/array.dfy"


module {:options "/functionSyntax:4"} DafnyArrays {
  import opened Arrays

  ///
  // Feasibility implementation
  // TODO: Move this to test/ or examples/,
  // especially since we don't want to compile any seq<T> values
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
      ret := new DafnyImmutableArray(ValuesFromArray(this, size));
    }
  }

  function ValuesFromArray<T>(a: Array<T>, size: nat): (ret: seq<T>)
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

  class DafnyImmutableArray<T> extends ImmutableArray<T> {

    const valuesSeq: seq<T>

    ghost predicate Valid() {
      values == valuesSeq
    }

    constructor(valuesSeq: seq<T>)
      ensures Valid()
      ensures this.valuesSeq == valuesSeq
    {
      this.values := valuesSeq;
      this.valuesSeq := valuesSeq;
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

    method Slice(start: nat, end: nat) returns (ret: ImmutableArray<T>)
      requires Valid()
      requires start <= end <= Length()
      ensures ret.Valid()
      ensures ret.Length() == end - start
      ensures forall i | 0 <= i < ret.Length() :: ret.At(i) == At(start + i)
    {
      return new DafnyImmutableArray(valuesSeq[start..end]);
    }
  }
}