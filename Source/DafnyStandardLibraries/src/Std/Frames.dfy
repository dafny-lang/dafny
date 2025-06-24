module Std.Frames {

  import opened Termination

  // A trait for objects with a Valid() predicate. Necessary in order to
  // generalize some proofs, but also useful for reducing the boilerplate
  // that most such objects need to include.
  trait Validatable extends object {
    // Ghost state tracking the common set of objects most
    // methods need to read.
    //
    // Note this is used as the decreases clause for Valid(),
    // but it is not necessarily the best choice for a decreases clause
    // for other methods on implementing types.
    // In particular, methods with loops that allocate new objects
    // probably can't use Repr, because even if constructors
    // ensure that the new object's Repr is fresh,
    // it is not possible to prove the actual proof obligation,
    // which is `old(Repr) decreases to (new object).Repr`.
    // See FramesExamples.dfy for a detailed example.
    //
    ghost var Repr: set<object>

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      decreases Repr, 0

    twostate predicate ValidChange()
      reads this, Repr
      ensures ValidChange() ==>
                old(Valid()) && Valid() && fresh(Repr - old(Repr))

    twostate lemma ValidImpliesValidChange()
      requires old(Valid())
      requires unchanged(old(Repr))
      ensures ValidChange()

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

    twostate predicate ValidComponentChange(component: Validatable)
      reads this, Repr
    {
      && ValidComponent(component)
      && component.ValidChange()
    }

    ghost function ReprTerminationMetric(): TerminationMetric
      reads this
    {
      TMSet(set o <- Repr :: TMObject(o))
    }

    // Convenience predicate, since you often want to assert that
    // new objects in Repr are fresh as well in most postconditions.
    // This is often at least necessary in ValidChange().
    twostate predicate ValidAndDisjoint()
      reads this, Repr
    {
      Valid() && fresh(Repr - old(Repr))
    }
  }

  // Simple classes holding onto an arbitrary mutable value.
  // Useful for working around the fact that mutable fields
  // are not first-class values as objects are:
  // You can't express something like
  //    `modifies Repr - {this`specialField}`
  // But you can say
  //    `modifies Repr - {this.specialFieldBox}`

  class GhostBox<T> {

    ghost var value: T

    ghost constructor (value: T)
      reads {}
      ensures this.value == value
    {
      this.value := value;
    }
  }

  class Box<T> {

    var value: T

    constructor (value: T)
      reads {}
      ensures this.value == value
    {
      this.value := value;
    }
  }
}