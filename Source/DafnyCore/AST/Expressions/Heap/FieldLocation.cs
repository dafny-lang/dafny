namespace Microsoft.Dafny;

/// <summary>
/// The right-hand-side of an expression of the type obj`fieldName
/// Denotes the memory location at this index
/// </summary>
public class FieldLocation : Expression, ICloneable<FieldLocation> {
  // Because memory locations are tuples, this is just a copy of the expression so that we can determine if
  public Name Name { get; }
  public Field Field { get; set; }

  public FieldLocation(Name name, Field field) : base(name.Origin) {
    this.Name = name;
    this.Field = field;
  }

  public FieldLocation(Cloner cloner, FieldLocation original) : base(cloner, original) {
    this.Field = original.Field;// We should not clone the field otherwise we loose precomputed visibility scopes
    this.Name = original.Name;
  }

  public FieldLocation Clone(Cloner cloner) {
    return new FieldLocation(cloner, this);
  }
}