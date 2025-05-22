using System.Collections.Generic;
using JetBrains.Annotations;

namespace Microsoft.Dafny;

/// <summary>
/// Representation of an expression like obj`fieldName or objSet`fieldName
/// If obj is a single object, resolves to FieldLocation
/// If obj is a set of objects, resolves to set x | x in ObjectCopy :: x`Name (FieldLocation)
/// Same for sequences or multisets
/// </summary>
public class FieldLocationExpression : SuffixExpr, ICloneable<FieldLocationExpression> {
  public Name Name { get; }

  [FilledInDuringResolution]
  public Field ResolvedField { get; set; }

  public Token Backtick { get; }

  public FieldLocationExpression(Expression lhs, Token backtick, Name name) : base(name.Origin, lhs) {
    this.Backtick = backtick;
    this.Name = name;
  }

  public FieldLocationExpression(Cloner cloner, FieldLocationExpression original) : base(cloner, original) {
    this.ResolvedField = original.ResolvedField != null
      ? cloner.CloneField(original.ResolvedField) : null;
    this.ResolvedExpression = original.ResolvedExpression != null
      ? cloner.CloneExpr(original.ResolvedExpression) : null;
    this.Name = original.Name;
    this.Backtick = original.Backtick;
  }

  public FieldLocationExpression Clone(Cloner cloner) {
    return new FieldLocationExpression(cloner, this);
  }

  public override IEnumerable<Expression> SubExpressions => ResolvedExpression == null ? PreResolveSubExpressions : [
    ResolvedExpression
  ];
}