using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class NestedMatchStmt : ConcreteSyntaxStatement, ICloneable<NestedMatchStmt> {
  public readonly Expression Source;
  public readonly List<NestedMatchCaseStmt> Cases;
  public readonly bool UsesOptionalBraces;

  private void InitializeAttributes() {
    // Default case for match is false
    bool splitMatch = Attributes.Contains(this.Attributes, "split");
    Attributes.ContainsBool(this.Attributes, "split", ref splitMatch);
    foreach (var c in this.Cases) {
      if (!Attributes.Contains(c.Attributes, "split")) {
        List<Expression> args = new List<Expression>();
        args.Add(new LiteralExpr(c.Tok, splitMatch));
        Attributes attrs = new Attributes("split", args, c.Attributes);
        c.Attributes = attrs;
      }
    }
  }

  public NestedMatchStmt Clone(Cloner cloner) {
    return new NestedMatchStmt(cloner, this);
  }

  public NestedMatchStmt(Cloner cloner, NestedMatchStmt original) : base(cloner, original) {
    Source = cloner.CloneExpr(original.Source);
    Cases = original.Cases.ConvertAll(cloner.CloneNestedMatchCaseStmt);
    UsesOptionalBraces = original.UsesOptionalBraces;
  }

  public override IEnumerable<INode> Children =>
    ResolvedStatement == null ? new[] { Source }.Concat<INode>(Cases) : base.Children;

  public override IEnumerable<Statement> SubStatements =>
    ResolvedStatement == null ? Cases.SelectMany(c => c.Body) : base.SubStatements;

  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in base.NonSpecificationSubExpressions) {
        yield return e;
      }
      yield return Source;
    }
  }

  public NestedMatchStmt(IToken tok, IToken endTok, Expression source, [Captured] List<NestedMatchCaseStmt> cases, bool usesOptionalBraces, Attributes attrs = null)
    : base(tok, endTok, attrs) {
    Contract.Requires(source != null);
    Contract.Requires(cce.NonNullElements(cases));
    this.Source = source;
    this.Cases = cases;
    this.UsesOptionalBraces = usesOptionalBraces;
    InitializeAttributes();
  }
}
