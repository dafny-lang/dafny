#nullable enable

using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class FrameExpression : NodeWithComputedRange, IHasReferences {
  public readonly Expression OriginalExpression; // may be a WildcardExpr
  [FilledInDuringResolution] public Expression? DesugaredExpression; // may be null for modifies clauses, even after resolution

  /// <summary>
  /// .E starts off as OriginalExpression; destructively updated to its desugared version during resolution
  /// </summary>
  public Expression E => DesugaredExpression ?? OriginalExpression;

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(E != null);
    Contract.Invariant(!(E is WildcardExpr) || (FieldName == null && Field == null));
  }

  public readonly string? FieldName;
  [FilledInDuringResolution] public Field? Field;  // null if FieldName is

  /// <summary>
  /// If a "fieldName" is given, then "tok" denotes its source location.  Otherwise, "tok"
  /// denotes the source location of "e".
  /// </summary>
  [SyntaxConstructor]
  public FrameExpression(IOrigin origin, Expression e, string? fieldName) : base(origin) {
    Contract.Requires(!(e is WildcardExpr) || fieldName == null);
    OriginalExpression = e;
    FieldName = fieldName;
  }

  public FrameExpression(Cloner cloner, FrameExpression original) : base(cloner, original) {
    OriginalExpression = cloner.CloneExpr(original.OriginalExpression);
    FieldName = original.FieldName;

    if (cloner.CloneResolvedFields) {
      Field = original.Field;
      if (original.DesugaredExpression != null) {
        DesugaredExpression = cloner.CloneExpr(original.DesugaredExpression);
      }
    }
  }

  public override IEnumerable<INode> Children => new[] { E };
  public override IEnumerable<INode> PreResolveChildren => Children;
  public IEnumerable<Reference> GetReferences() {
    return Field == null ? Enumerable.Empty<Reference>() : new[] { new Reference(Origin, Field) };
  }
}