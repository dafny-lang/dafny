namespace Microsoft.Dafny;

/// <summary>
/// The right-hand-side of an expression of the type obj`fieldName
/// Denotes the memory location at this index
/// </summary>
public class FieldLocation: Expression, ICloneable<FieldLocation> {
  // Because memory locations are tuples, this is just a copy of the expression so that we can determine if
  // it's legit to 
  public Expression ObjectCopy { get; }
  public Name Name { get; }
  
  [FilledInDuringResolution]
  public Field ResolvedField { get; set; }
  
  public FieldLocation(Expression objectCopy, Name name) : base(name.Origin) {
    this.ObjectCopy = objectCopy;
    this.Name = name;
  }

  public FieldLocation(Cloner cloner, FieldLocation original) : base(cloner, original) {
    this.ObjectCopy = cloner.CloneExpr(original.ObjectCopy);
    this.ResolvedField = original.ResolvedField != null
      ? cloner.CloneField(original.ResolvedField) : null;
    this.Name = original.Name;
  }

  public FieldLocation Clone(Cloner cloner) {
    return new FieldLocation(cloner, this);
  }
}