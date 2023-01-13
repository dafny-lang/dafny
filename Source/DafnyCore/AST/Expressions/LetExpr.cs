using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public class LetExpr : Expression, IAttributeBearingDeclaration, IBoundVarsBearingExpression, ICloneable<LetExpr> {
  public readonly List<CasePattern<BoundVar>> LHSs;
  public readonly List<Expression> RHSs;
  public readonly Expression Body;
  public readonly bool Exact;  // Exact==true means a regular let expression; Exact==false means an assign-such-that expression
  public readonly Attributes Attributes;
  Attributes IAttributeBearingDeclaration.Attributes => Attributes;
  [FilledInDuringResolution] public List<ComprehensionExpr.BoundedPool> Constraint_Bounds;  // null for Exact=true and for when expression is in a ghost context
  // invariant Constraint_Bounds == null || Constraint_Bounds.Count == BoundVars.Count;
  private Expression translationDesugaring;  // filled in during translation, lazily; to be accessed only via Translation.LetDesugaring; always null when Exact==true
  private Translator lastTranslatorUsed; // avoid clashing desugaring between translators

  public void SetTranslationDesugaring(Translator trans, Expression expr) {
    lastTranslatorUsed = trans;
    translationDesugaring = expr;
  }

  public Expression GetTranslationDesugaring(Translator trans) {
    if (lastTranslatorUsed == trans) {
      return translationDesugaring;
    } else {
      return null;
    }
  }

  public LetExpr Clone(Cloner cloner) {
    return new LetExpr(cloner, this);
  }

  public LetExpr(Cloner cloner, LetExpr original) : base(cloner, original) {
    LHSs = original.LHSs.ConvertAll(cloner.CloneCasePattern);
    RHSs = original.RHSs.ConvertAll(cloner.CloneExpr);
    Body = cloner.CloneExpr(original.Body);
    Exact = original.Exact;
    Attributes = cloner.CloneAttributes(original.Attributes);
    if (cloner.CloneResolvedFields) {
      Constraint_Bounds = original.Constraint_Bounds;
    }
  }

  public LetExpr(IToken tok, List<CasePattern<BoundVar>> lhss, List<Expression> rhss, Expression body, bool exact, Attributes attrs = null)
    : base(tok) {
    LHSs = lhss;
    RHSs = rhss;
    Body = body;
    Exact = exact;
    Attributes = attrs;
  }
  public override IEnumerable<Expression> SubExpressions {
    get {
      foreach (var e in Attributes.SubExpressions(Attributes)) {
        yield return e;
      }
      foreach (var rhs in RHSs) {
        yield return rhs;
      }
      yield return Body;
    }
  }

  public override IEnumerable<Type> ComponentTypes => BoundVars.Select(bv => bv.Type);

  public IEnumerable<BoundVar> BoundVars {
    get {
      foreach (var lhs in LHSs) {
        foreach (var bv in lhs.Vars) {
          yield return bv;
        }
      }
    }
  }

  public IEnumerable<BoundVar> AllBoundVars => BoundVars;

  public override IEnumerable<INode> Children =>
    (Attributes != null ? new List<INode> { Attributes } : Enumerable.Empty<INode>())
    .Concat(LHSs)
    .Concat(base.Children);
}