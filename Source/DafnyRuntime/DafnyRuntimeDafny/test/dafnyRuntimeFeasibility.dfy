
include "../src/dafnyRuntime.dfy"

// Implementing the external traits to guard against inconsistent specifications
module {:options "/functionSyntax:4"} FeasibilityImplementation refines Dafny {

  class DafnyNativeArray<T> extends NativeArray<T> {
    const valuesArray: array<ArrayCell<T>>

    ghost predicate Valid()
      reads this, Repr
      decreases Repr, 1
      ensures Valid() ==> this in Repr
      ensures Valid() ==> |values| < SIZE_T_LIMIT
    {
      && Repr == {this, valuesArray}
      && valuesArray[..] == values
      && |values| < SIZE_T_LIMIT
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

    function Length(): size_t
      requires Valid()
      reads Repr
      ensures Length() as int == |values|
    {
      valuesArray.Length as size_t
    }

    function Select(i: size_t): (ret: T)
      requires Valid()
      requires i < Length()
      requires values[i].Set?
      reads this, Repr
      ensures ret == values[i].value
    {
      valuesArray[i].value
    }

    method Update(i: size_t, t: T)
      requires Valid()
      requires i < Length()
      modifies Repr
      ensures ValidAndDisjoint()
      ensures Repr == old(Repr)
      ensures Length() == old(Length())
      ensures values == old(values)[..i] + [Set(t)] + old(values)[(i + 1)..]
      ensures Select(i) == t
    {
      valuesArray[i] := Set(t);

      values := valuesArray[..];
    }

    method UpdateSubarray(start: size_t, other: ImmutableArray<T>)
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
        valuesArray[start + i] := Set(other.Select(i));
      }
      values := valuesArray[..];
    }

    method Freeze(size: size_t) returns (ret: ImmutableArray<T>)
      requires Valid()
      requires size <= Length()
      requires forall i | 0 <= i < size :: values[i].Set?
      ensures ret.Valid()
      ensures |ret.values| == size as int
      ensures forall i | 0 <= i < size :: ret.values[i] == values[i].value
    {
      ret := new DafnyImmutableArray(ValuesFromArray(this, size));
    }
  }

  function ValuesFromArray<T>(a: DafnyNativeArray<T>, size: size_t): (ret: seq<T>)
    requires a.Valid()
    requires size <= a.Length()
    requires forall i | 0 <= i < size :: a.values[i].Set?
    reads a, a.Repr
    ensures |ret| == size as int
    ensures forall i | 0 <= i < size :: ret[i] == a.values[i].value
  {
    if size == 0 then
      []
    else
      ValuesFromArray(a, size - 1) + [a.Select(size - 1)]
  }

  class DafnyImmutableArray<T> extends ImmutableArray<T> {

    const valuesSeq: seq<T>

    ghost predicate Valid() 
      ensures Valid() ==> |values| < SIZE_T_LIMIT
    {
      && values == valuesSeq
      && |values| < SIZE_T_LIMIT
    }

    constructor(valuesSeq: seq<T>)
      requires |valuesSeq| < SIZE_T_LIMIT
      ensures Valid()
      ensures this.valuesSeq == valuesSeq
    {
      this.values := valuesSeq;
      this.valuesSeq := valuesSeq;
    }

    function Length(): size_t 
      requires Valid()
      ensures Length() as int == |values|
    {
      |valuesSeq| as size_t
    }

    function Select(index: size_t): T
      requires Valid()
      requires index as int < |values|
      ensures Select(index) == values[index]
    {
      valuesSeq[index]
    }

    method Subarray(lo: size_t, hi: size_t) returns (ret: ImmutableArray<T>)
      requires Valid()
      requires lo <= hi <= Length()
      ensures ret.Valid()
      ensures ret.Length() == hi - lo
      ensures ret.values == values[lo..hi]
    {
      return new DafnyImmutableArray(valuesSeq[lo..hi]);
    }
  }
}