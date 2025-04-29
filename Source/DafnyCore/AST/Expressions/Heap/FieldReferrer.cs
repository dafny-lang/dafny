namespace Microsoft.Dafny;

/// <summary>
/// The right-hand-side of an expression of the type obj`fieldName
/// Denotes the memory location at this index
/// </summary>
public class FieldReferrer: Expression, ICloneable<FieldReferrer> {
  // Because memory locations are tuples, this is just a copy of the expression so that we can determine if
  // it's legit to 
  public Expression ObjectCopy { get; }
  public Name Name { get; }
  
  public FieldReferrer(Expression objectCopy, Name name) : base(name.Origin) {
    this.ObjectCopy = objectCopy;
    this.Name = name;
  }

  public FieldReferrer(Cloner cloner, FieldReferrer original) : base(cloner, original) {
    this.ObjectCopy = cloner.CloneExpr(original.ObjectCopy);
    this.Name = original.Name;
  }

  public FieldReferrer Clone(Cloner cloner) {
    return new FieldReferrer(cloner, this);
  }
}