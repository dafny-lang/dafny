
include "array.dfy"
include "frames.dfy"

module {:options "/functionSyntax:4"} AtomicBoxes {
  import opened Arrays
  import opened Frames

  trait {:termination false} AtomicBox<T> extends Validatable {

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> Repr == {}

    ghost const inv: T -> bool

    method {:extern} Put(t: T)
      requires inv(t)

    method {:extern} Get() returns (t: T)
      ensures inv(t)
  }

  // Feasibility implementation
  // DO NOT USE THIS as it is not guaranteed to be atomic!
  //
  // Using Array<T> as an arbitrary type that needs an invariant.
  // class DafnyNotActuallyAtomicBox<T> extends AtomicBox<Array<T>> {

  //   var value: Array<T>

  //   constructor(inv: Array<T> -> bool, value: Array<T>) 
  //     requires inv(value)
  //   {
  //     this.inv := inv;
  //     this.value := value;
  //   }

  //   method Put(value: Array<T>)
  //     requires inv(value)
  //   {
  //     this.value := value;
  //   }

  //   method Get() returns (value: Array<T>)
  //     ensures inv(value)
  //   {
  //     return this.value;
  //   }
  // }
}