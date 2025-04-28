namespace Microsoft.Dafny;

/// <summary>
/// The right-hand-side of an expression of the type obj`fieldName
/// Denotes the memory location at this index
/// </summary>
public class FieldReferrer: Expression {
  public Name Name { get; set; }
  
  public FieldReferrer(Name name) : base(name.Origin)
  {
    this.Name = name;
  }

  public FieldReferrer(Cloner cloner, FieldReferrer original) : base(cloner, original)
  {
    this.Name = original.Name;
  }
}