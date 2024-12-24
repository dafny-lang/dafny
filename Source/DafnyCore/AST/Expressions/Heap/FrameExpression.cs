using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class FrameExpression : TokenNode, IHasReferences {
  public readonly Expression OriginalExpression; // may be a WildcardExpr
  [FilledInDuringResolution] public Expression DesugaredExpression; // may be null for modifies clauses, even after resolution

  /// <summary>
  /// .E starts off as OriginalExpression; destructively updated to its desugared version during resolution
  /// </summary>
  public Expression E => DesugaredExpression ?? OriginalExpression;

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(E != null);
    Contract.Invariant(!(E is WildcardExpr) || (FieldName == null && Field == null));
  }

  public readonly string FieldName;
  [FilledInDuringResolution] public Field Field;  // null if FieldName is

  /// <summary>
  /// If a "fieldName" is given, then "tok" denotes its source location.  Otherwise, "tok"
  /// denotes the source location of "e".
  /// </summary>
  public FrameExpression(IOrigin tok, Expression e, string fieldName) {
    Contract.Requires(tok != null);
    Contract.Requires(e != null);
    Contract.Requires(!(e is WildcardExpr) || fieldName == null);
    this.tok = tok;
    OriginalExpression = e;
    FieldName = fieldName;
  }

  public FrameExpression(Cloner cloner, FrameExpression original) {
    this.tok = cloner.Origin(original.Tok);
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
    return Field == null ? Enumerable.Empty<Reference>() : new[] { new Reference(Tok, Field) };
  }
}