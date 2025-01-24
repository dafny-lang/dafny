module Frames {

  // A trait for objects with a Valid() predicate. Necessary in order to
  // generalize some proofs, but also useful for reducing the boilerplate
  // that most such objects need to include.
  trait Validatable {
    // Ghost state tracking the common set of objects most
    // methods need to read.
    ghost var Repr: set<object>
    ghost const height: nat

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      decreases height, 0

    // Convenience predicate for when your object's validity depends on one
    // or more other objects.
    ghost predicate ValidComponent(component: Validatable)
      reads this, Repr
    {
      && component in Repr
      && component.Repr <= Repr
      && this !in component.Repr
      && component.Valid()
      && component.height < height
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