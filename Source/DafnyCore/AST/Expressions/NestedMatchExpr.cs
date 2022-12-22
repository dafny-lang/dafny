using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class NestedMatchExpr : ConcreteSyntaxExpression {
  public readonly Expression Source;
  public readonly List<NestedMatchCaseExpr> Cases;
  public readonly bool UsesOptionalBraces;
  public Attributes Attributes;

  public NestedMatchExpr(IToken tok, Expression source, [Captured] List<NestedMatchCaseExpr> cases, bool usesOptionalBraces, Attributes attrs = null) : base(tok) {
    Contract.Requires(source != null);
    Contract.Requires(cce.NonNullElements(cases));
    this.Source = source;
    this.Cases = cases;
    this.UsesOptionalBraces = usesOptionalBraces;
    this.Attributes = attrs;
  }

  public override IEnumerable<Expression> SubExpressions =>
    ResolvedExpression == null ? new[] { Source }.Concat(Cases.Select(c => c.Body)) : base.SubExpressions;

  public override IEnumerable<INode> Children => ResolvedExpression == null
    ? new[] { Source }.Concat<INode>(Cases)
    : base.Children;
}
