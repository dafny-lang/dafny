using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

/// <summary>
/// The parsing and resolution/type checking of expressions of the forms
///   0. ident &lt; Types &gt;
///   1. Expr . ident &lt; Types &gt;
///   2. Expr ( Exprs )
///   3. Expr [ Exprs ]
///   4. Expr [ Expr .. Expr ]
/// is done as follows.  These forms are parsed into the following AST classes:
///   0. NameSegment
///   1. ExprDotName
///   2. ApplySuffix
///   3. SeqSelectExpr or MultiSelectExpr
///   4. SeqSelectExpr
///
/// The first three of these inherit from ConcreteSyntaxExpression.  The resolver will resolve
/// these into:
///   0. IdentifierExpr or MemberSelectExpr (with .Lhs set to ImplicitThisExpr or StaticReceiverExpr)
///   1. IdentifierExpr or MemberSelectExpr
///   2. FuncionCallExpr or ApplyExpr
///
/// The IdentifierExpr's that forms 0 and 1 can turn into sometimes denote the name of a module or
/// type.  The .Type field of the corresponding resolved expressions are then the special Type subclasses
/// ResolutionType_Module and ResolutionType_Type, respectively.  These will not be seen by the
/// verifier or compiler, since, in a well-formed program, the verifier and compiler will use the
/// .ResolvedExpr field of whatever form-1 expression contains these.
///
/// Notes:
///   * IdentifierExpr and FunctionCallExpr are resolved-only expressions (that is, they don't contain
///     all the syntactic components that were used to parse them).
///   * Rather than the current SeqSelectExpr/MultiSelectExpr split of forms 3 and 4, it would
///     seem more natural to refactor these into 3: IndexSuffixExpr and 4: RangeSuffixExpr.
/// </summary>
public abstract class SuffixExpr : ConcreteSyntaxExpression {
  public Expression Lhs;

  protected SuffixExpr(Cloner cloner, SuffixExpr original) : base(cloner, original) {
    Lhs = cloner.CloneExpr(original.Lhs);
  }

  [SyntaxConstructor]
  protected SuffixExpr(IOrigin origin, Expression lhs)
    : base(origin) {
    Contract.Requires(origin != null);
    Contract.Requires(lhs != null);
    Lhs = lhs;
  }

  public override IEnumerable<INode> Children => ResolvedExpression == null ? new[] { Lhs } : base.Children;
  public override IEnumerable<INode> PreResolveChildren => PreResolveSubExpressions;

  public override IEnumerable<Expression> SubExpressions {
    get {
      if (!WasResolved()) {
        foreach (var sub in PreResolveSubExpressions) {
          yield return sub;
        }
      } else if (Resolved != null) {
        yield return Resolved;
      }
    }
  }

  public override IEnumerable<Expression> PreResolveSubExpressions {
    get {
      yield return Lhs;
    }
  }
}