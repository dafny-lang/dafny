#nullable enable

using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class FrameExpression : NodeWithOrigin, IHasReferences {
  public Expression OriginalExpression { get; } // may be a WildcardExpr
  [FilledInDuringResolution] public Expression? DesugaredExpression; // may be null for modifies clauses, even after resolution

  /// <summary>
  /// .E starts off as OriginalExpression; destructively updated to its desugared version during resolution
  /// </summary>
  public Expression E => DesugaredExpression ?? OriginalExpression;

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(!(E is WildcardExpr) || (FieldName == null && Field == null));
  }

  public string? FieldName;
  [FilledInDuringResolution] public Field? Field;  // null if FieldName is

  /// <summary>
  /// If a "fieldName" is given, then "tok" denotes its source location.  Otherwise, "tok"
  /// denotes the source location of "e".
  /// </summary>
  [SyntaxConstructor]
  public FrameExpression(IOrigin origin, Expression originalExpression, string? fieldName) : base(origin) {
    Contract.Requires(!(originalExpression is WildcardExpr) || fieldName == null);
    OriginalExpression = originalExpression;
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
    return Field == null ? Enumerable.Empty<Reference>() : new[] { new Reference(ReportingRange, Field) };
  }
}