using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

/// <summary>
/// The right-hand-side of an expression of the type obj`fieldName
/// Denotes the memory location at this index
/// </summary>
public class FieldLocation : Expression, ICloneable<FieldLocation> {
  public Name Name { get; }
  public Field Field { get; set; }

  // Relevant only when the field is a SpecialField and has an EnclosingMethod
  public bool AtCallSite { get; set; }

  public FieldLocation(Name name, Field field, bool atCallSite) : base(name.Origin) {
    Contract.Requires(atCallSite == false || field is SpecialField { EnclosingMethod: not null });
    this.Name = name;
    this.Field = field;
    this.AtCallSite = atCallSite;
  }

  public FieldLocation(Cloner cloner, FieldLocation original) : base(cloner, original) {
    this.Field = original.Field;// We should not clone the field otherwise we loose precomputed visibility scopes
    this.Name = original.Name;
    this.AtCallSite = original.AtCallSite;
  }

  public FieldLocation Clone(Cloner cloner) {
    return new FieldLocation(cloner, this);
  }
}