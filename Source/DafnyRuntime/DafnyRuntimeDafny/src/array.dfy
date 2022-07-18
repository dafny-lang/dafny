

module {:options "/functionSyntax:4"} Arrays {

  // A trait for objects with a Valid() predicate. Necessary in order to
  // generalize some proofs, but also useful for reducing the boilerplate
  // that most such objects need to include.
  trait {:termination false} Validatable {
    // Ghost state tracking the common set of objects most
    // methods need to read.
    ghost var Repr: set<object>

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr

    // Convenience predicate for when your object's validity depends on one
    // or more other objects.
    ghost predicate ValidComponent(component: Validatable)
      reads this, Repr 
    {
      && component in Repr
      && component.Repr <= Repr
      && this !in component.Repr
      && component.Valid()
    }

    // Convenience predicate, since you often want to assert that 
    // new objects in Repr are fresh as well in most postconditions.
    twostate predicate ValidAndDisjoint()
      reads this, Repr
    {
      Valid() && fresh(Repr - old(Repr))
    }
  }

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
}