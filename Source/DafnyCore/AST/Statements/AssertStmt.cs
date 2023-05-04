using System.Collections.Generic;
using System.Diagnostics.Contracts;
using Microsoft.Dafny.Auditor;

namespace Microsoft.Dafny;

public class AssertStmt : PredicateStmt, ICloneable<AssertStmt>, ICanFormat {
  public readonly BlockStmt Proof;
  public readonly AssertLabel Label;

  public AssertStmt Clone(Cloner cloner) {
    return new AssertStmt(cloner, this);
  }

  public AssertStmt(Cloner cloner, AssertStmt original) : base(cloner, original) {
    Proof = cloner.CloneBlockStmt(original.Proof);
    Label = original.Label == null ? null : new AssertLabel(cloner.Tok(original.Label.Tok), original.Label.Name);
  }

  public static AssertStmt CreateErrorAssert(INode node, string message, Expression guard = null) {
    var errorMessage = new StringLiteralExpr(node.Tok, message, true);
    errorMessage.Type = new SeqType(Type.Char);
    var attr = new Attributes("error", new List<Expression> { errorMessage }, null);
    guard ??= Expression.CreateBoolLiteral(node.Tok, false);
    var assertFalse = new AssertStmt(node.RangeToken, guard, null, null, attr);
    assertFalse.IsGhost = true;
    return assertFalse;
  }

  public AssertStmt(RangeToken rangeToken, Expression expr, BlockStmt/*?*/ proof, AssertLabel/*?*/ label, Attributes attrs)
    : base(rangeToken, expr, attrs) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(expr != null);
    Proof = proof;
    Label = label;
  }

  public override IEnumerable<Statement> SubStatements {
    get {
      if (Proof != null) {
        yield return Proof;
      }
    }
  }
  public void AddCustomizedErrorMessage(IToken tok, string s) {
    var args = new List<Expression>() { new StringLiteralExpr(tok, s, true) };
    IToken openBrace = tok;
    IToken closeBrace = new Token(tok.line, tok.col + 7 + s.Length + 1); // where 7 = length(":error ")
    this.Attributes = new UserSuppliedAttributes(tok, openBrace, closeBrace, args, this.Attributes);
  }

  public override IEnumerable<Expression> SpecificationSubExpressions {
    get {
      foreach (var e in base.SpecificationSubExpressions) { yield return e; }
      yield return Expr;
    }
  }

  public override IEnumerable<Assumption> Assumptions(Declaration decl) {
    if (Attributes.Contains(Attributes, "only")) {
      yield return new Assumption(decl, tok, AssumptionDescription.AssertOnly);
    }
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    return formatter.SetIndentAssertLikeStatement(this, indentBefore);
  }

  public bool HasAssertOnlyAttribute(out AssertOnlyKind assertOnlyKind) {

    assertOnlyKind = AssertOnlyKind.Single;
    if (Attributes.Find(Attributes, "only") is not UserSuppliedAttributes attribute) {
      return false;
    }

    if (attribute.Args.Count != 1 || attribute.Args[0] is not LiteralExpr { Value: var value }) {
      return true;
    }

    assertOnlyKind = value switch {
      "before" => AssertOnlyKind.Before,
      "after" => AssertOnlyKind.After,
      _ => assertOnlyKind
    };

    return true;
  }

  public enum AssertOnlyKind {
    Before,
    After,
    Single
  }
}

