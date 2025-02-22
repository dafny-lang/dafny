using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Numerics;
using System.Linq;
using JetBrains.Annotations;

namespace Microsoft.Dafny;

/// <summary>
/// A ComprehensionExpr has the form:
///   BINDER { x [: Type] [<- Domain] [Attributes] [| Range] } [:: Term(x)]
/// Where BINDER is currently "forall", "exists", "iset"/"set", or "imap"/"map".
///
/// Quantifications used to only support a single range, but now each
/// quantified variable can have a range attached.
/// The overall Range is now filled in by the parser by extracting any implicit
/// "x in Domain" constraints and per-variable Range constraints into a single conjunct.
///
/// The Term is optional if the expression only has one quantified variable,
/// but required otherwise.
///
/// LambdaExpr also inherits from this base class but isn't really a comprehension,
/// and should be considered implementation inheritance.
/// </summary>
public abstract partial class ComprehensionExpr : Expression, IAttributeBearingDeclaration, IBoundVarsBearingExpression, ICanFormat {
  public virtual string WhatKind => "comprehension";
  public readonly List<BoundVar> BoundVars;
  public readonly Expression Range;
  public Expression Term;

  public IEnumerable<BoundVar> AllBoundVars => BoundVars;

  public IOrigin BodyStartOrigin = Token.NoToken;

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(BoundVars != null);
    Contract.Invariant(Term != null);
  }

  public Attributes Attributes;
  Attributes IAttributeBearingDeclaration.Attributes {
    get => Attributes;
    set => Attributes = value;
  }

  [FilledInDuringResolution] public List<BoundedPool> Bounds;
  // invariant Bounds == null || Bounds.Count == BoundVars.Count;

  public List<BoundVar> UncompilableBoundVars() {
    Contract.Ensures(Contract.Result<List<BoundVar>>() != null);
    var v = BoundedPool.PoolVirtues.Finite | BoundedPool.PoolVirtues.Enumerable;
    return BoundedPool.MissingBounds(BoundVars, Bounds, v);
  }

  protected ComprehensionExpr(IOrigin origin, List<BoundVar> bvars, Expression range, Expression term, Attributes attrs)
    : base(origin) {
    Contract.Requires(origin != null);
    Contract.Requires(cce.NonNullElements(bvars));
    Contract.Requires(term != null);

    BoundVars = bvars;
    Range = range;
    Term = term;
    Attributes = attrs;
    BodyStartOrigin = origin;
  }

  protected ComprehensionExpr(Cloner cloner, ComprehensionExpr original) : base(cloner, original) {
    BoundVars = original.BoundVars.Select(bv => cloner.CloneBoundVar(bv, false)).ToList();
    Range = cloner.CloneExpr(original.Range);
    Attributes = cloner.CloneAttributes(original.Attributes);
    BodyStartOrigin = cloner.Origin(original.BodyStartOrigin);
    Term = cloner.CloneExpr(original.Term);

    if (cloner.CloneResolvedFields) {
      Bounds = original.Bounds?.Select(b => b?.Clone(cloner)).ToList();
    }
  }
  public override IEnumerable<INode> Children =>
    Attributes.AsEnumerable().
    Concat<Node>(BoundVars).Concat(SubExpressions);

  public override IEnumerable<INode> PreResolveChildren =>
    Attributes.AsEnumerable()
      .Concat<Node>(Range != null && Range.Origin.line > 0 ? [Range] : new List<Node>())
    .Concat(Term != null && Term.Origin.line > 0 ? [Term] : new List<Node>());

  public override IEnumerable<Expression> SubExpressions {
    get {
      foreach (var e in Attributes.SubExpressions(Attributes)) {
        yield return e;
      }
      if (Range != null) { yield return Range; }
      yield return Term;
    }
  }

  public override IEnumerable<Type> ComponentTypes => BoundVars.Select(bv => bv.Type);
  public virtual bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    var alreadyAligned = false;
    var assignOpIndent = indentBefore;

    foreach (var token in OwnedTokens) {
      switch (token.val) {
        case "forall":
        case "exists":
        case "map":
        case "set":
        case "imap":
        case "iset": {
            indentBefore = formatter.ReduceBlockiness ? indentBefore : formatter.GetNewTokenVisualIndent(token, indentBefore);
            assignOpIndent = formatter.ReduceBlockiness ? indentBefore + formatter.SpaceTab : indentBefore;
            formatter.SetOpeningIndentedRegion(token, indentBefore);

            break;
          }
        case ":=":
        case "::": {
            var afterAssignIndent = (formatter.ReduceBlockiness && token.Prev.line == token.line) || token.line == token.Next.line ? assignOpIndent : assignOpIndent + formatter.SpaceTab;
            if (alreadyAligned) {
              formatter.SetIndentations(token, afterAssignIndent, assignOpIndent, afterAssignIndent);
            } else {
              if (TokenNewIndentCollector.IsFollowedByNewline(token)) {
                formatter.SetIndentations(token, afterAssignIndent, assignOpIndent, afterAssignIndent);
              } else {
                alreadyAligned = true;
                formatter.SetAlign(assignOpIndent, token, out afterAssignIndent, out assignOpIndent);
                assignOpIndent -= 1; // because "::" or ":=" has one more char than a comma 
              }
            }
            break;
          }
      }
    }

    return true;
  }
}
