module SeparatedClasses {
  trait {:termination false} OwnedObject {
    // Faking the built-in .Owner field.
    ghost var Owner: OwnedObject?

    ghost method SetOwner(o: OwnedObject, owner: OwnedObject?)
      requires CanAccess(o)
      modifies o`Owner
      ensures o.Owner == owner
    {
      o.Owner := owner;
    }

    ghost static method StaticSetOwner(ref: OwnedObject, owner: OwnedObject?) 
      requires StaticCanAccess(ref)
      modifies ref`Owner
      ensures ref.Owner == owner
    {
      ref.Owner := owner;
    }

    ghost predicate CanAccess(ref: OwnedObject) 
      reads this, ref
    {
      || ref == this
      || (ref != this && ref.Owner == this)
      || (ref != this && ref.Owner == this.Owner && ref.Owner != ref)
    }

    ghost static predicate StaticCanAccess(ref: OwnedObject) 
      reads ref
    {
      ref.Owner == null
    }

    // Hack to approximate how framing will work for separated classes:
    // if you don't own an object, you can't directly read or write it,
    // but you also therefore can ignore it in your reads and modifies clauses.
    // Use with caution: very easy to prove false with this!
    lemma {:axiom} IgnoreFraming(o: OwnedObject) 
      requires o.Owner != this
      ensures fresh(o)
    {
      assume {:axiom} fresh(o);
    }
  }

  class OwnedArray<T> extends OwnedObject {
    const a: array<T>

    constructor(a: array<T>) 
      ensures this.a == a
    {
      this.a := a;
    }
  }
}