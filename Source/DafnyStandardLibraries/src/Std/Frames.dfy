module Std.Frames {

  import opened Termination

  // A trait for objects with a Valid() predicate. Necessary in order to
  // generalize some proofs, but also useful for reducing the boilerplate
  // that most such objects need to include.
  trait Validatable {
    // Ghost state tracking the common set of objects most
    // methods need to read.
    //
    // TODO: (clean up the following)
    // Note this is used as the decreases clause for Valid(),
    // but it is not necessarily the best choice for a decreases clause
    // for other methods on implementing types.
    // In particular, methods with loops that allocate new objects
    // probably can't use Repr, because even if constructors
    // ensure that the new object's Repr is fresh,
    // it is not possible to prove the actual decreases to proof obligation,
    // which is old(Repr) decreases to (new object).Repr.
    //
    // TODO: Okay it's now or never - Repr or repr?? :)
    ghost var Repr: set<object>

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      decreases Repr, 0

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

    ghost function ReprTerminationMetric(): TerminationMetric
      reads this
    {
      TMSet(set o <- Repr :: TMObject(o))
    }

    // Convenience predicate, since you often want to assert that
    // new objects in Repr are fresh as well in most postconditions.
    twostate predicate ValidAndDisjoint()
      reads this, Repr
    {
      Valid() && fresh(Repr - old(Repr))
    }
  }
}