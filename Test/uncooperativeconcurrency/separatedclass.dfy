module SeparatedClasses {

  trait {:termination false} OwnedObject {
    // Faking the built-in .Owner field.
    ghost var Owner: OwnedObject?

    ghost method SetOwner(o: OwnedObject, owner: OwnedObject?)
      requires ThisCanAccess(o)
      modifies o`Owner
      ensures o.Owner == owner
    {
      o.Owner := owner;
    }

    ghost static method StaticSetOwner(ref: OwnedObject, owner: OwnedObject?) 
      requires CanAccess(null, ref)
      modifies ref`Owner
      ensures ref.Owner == owner
    {
      ref.Owner := owner;
    }

    ghost predicate ThisCanAccess(ref: OwnedObject) 
      reads this, ref
    {
      ref.Owner == this.Owner
    }

    ghost static predicate CanAccess(context: OwnedObject?, ref: OwnedObject) 
      reads context, ref
    {
      if context == null then
        ref.Owner == null
      else
        context.ThisCanAccess(ref)
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

  class Field<T> {
    ghost const Parent: OwnedObject;
    var value: T

    constructor(parent: OwnedObject, value: T) {
      this.value := value;
      Parent := parent;
    }

    method Read(context: OwnedObject?) returns (t: T)
      requires OwnedObject.CanAccess(context, Parent)
    {
      return value;
    }

    method Write(context: OwnedObject?, newValue: T)
      requires OwnedObject.CanAccess(context, Parent)
    {
      this.value := newValue;
    }
  }
}