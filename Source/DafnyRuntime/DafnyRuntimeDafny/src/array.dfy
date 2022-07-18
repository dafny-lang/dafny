include "frames.dfy"

module {:options "/functionSyntax:4"} Arrays {

  import opened Frames

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

  datatype InitializedArray<T> = InitializedArray(a: Array<T>) {
    ghost predicate Valid() reads a, a.Repr {
      && a.Valid()
      && forall i | 0 <= i < a.Length() :: a.values[i].Set?
    }
    ghost function Value(): seq<T> 
      requires Valid()
      reads a, a.Repr
    {
      seq(a.Length(), i requires Valid() && 0 <= i < a.Length() reads a, a.Repr => a.Read(i))
    }
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

  class ResizableArray<T> extends Validatable {
    const storage: Array<T>
    var size: nat

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
      ensures Remaining() == length
      ensures fresh(Repr)
    {
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

    ghost function Remaining(): nat
      requires Valid()
      reads this, Repr
    {
      storage.Length() - size
    }

    function Last(): T 
      requires Valid()
      requires 0 < size
      reads this, Repr
    {
      storage.Read(size - 1)
    }

    method AddLast(t: T) 
      requires Valid()
      requires size + 1 <= storage.Length()
      modifies Repr
      ensures ValidAndDisjoint()
      ensures Value() == old(Value()) + [t]
      ensures Remaining() == old(Remaining()) - 1
    {
      storage.Write(size, t);
      size := size + 1;
    }

    method RemoveLast() returns (t: T) 
      requires Valid()
      requires 0 < size
      modifies Repr
      ensures ValidAndDisjoint()
      ensures Value() == old(Value()[..(size - 1)])
      ensures Remaining() == old(Remaining()) + 1
    {
      t := storage.Read(size - 1);
      size := size - 1;
    }

    method Append(other: InitializedArray<T>) 
      requires Valid()
      requires other.Valid()
      requires Repr !! other.a.Repr
      requires size + other.a.Length() <= storage.Length()
      modifies Repr
      ensures ValidAndDisjoint()
      ensures Value() == old(Value()) + other.Value()
      ensures Remaining() == old(Remaining()) - other.a.Length()
    {
      storage.WriteRangeArray(size, other.a, 0, other.a.Length());
      size := size + other.a.Length();
    }
  }
}