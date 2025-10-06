using System.Collections.Generic;
using System.Linq;
using JetBrains.Annotations;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

// An invariant is...
public class Invariant([NotNull] IOrigin origin, [NotNull] List<AttributedExpression> clauses)
  : Predicate(origin,
    new(origin, "invariant"), // a predicate named "invariant"
    false, // that is not static
    true, // that is ghost
    false, // that is not opaque
    [], // has no type-, in-, or out-parameters
    [],
    null,
    [], // has no preconditions
    new([new(origin, new ThisExpr(origin), null)], null), // currently only reads "this"
    [], // has no postconditions
    new([Expression.CreateIntLiteralNonnegative(origin, 0)], null), // decreases 0 (is not recursive)
    clauses.Aggregate(Expression.CreateBoolLiteral(origin, true),
      Expression (acc, clause) => Expression.CreateAnd(acc, clause.E)), // whose body is all of the invariant clauses pasted together
    BodyOriginKind.OriginalOrInherited,
    null, // and has no by-method component
    null,
    null,
    null) {
  
  // We use the clauses of the invariant during the rewriting phase (to insert the invariant at the top and bottom of each method) to preserve its attributes
  public readonly List<AttributedExpression> Clauses = clauses;
  
  // A *mention* of the invariant is an ordinary reference to it
  public Expression Mention(IOrigin origin, Expression receiver, SystemModuleManager systemModuleManager) =>
    Expression.CreateResolvedCall(origin, receiver, this, [], [], systemModuleManager);
  
  // A *use* of the invariant (i.e., to assume or assert it) consists of determining whether the receiver is/is not in the open set OR the mention of its invariant is actually true
  public Expression Use(IOrigin origin, Expression receiver, SystemModuleManager systemModuleManager, BoogieGenerator.ExpressionTranslator etran, BoundVariable bv = null) {
    Expression openExprDafny;
    if (bv is null) {
      etran.OpenFormal(origin, out _, out openExprDafny);
    } else {
      openExprDafny = new BoogieGenerator.BoogieWrapper(new Boogie.IdentifierExpr(origin, bv), systemModuleManager.NonNullObjectSetType(origin));
    }
    return new BinaryExpr(origin, BinaryExpr.ResolvedOpcode.Or,
      new BinaryExpr(origin, BinaryExpr.ResolvedOpcode.InSet, receiver, openExprDafny),
      Mention(origin, receiver, systemModuleManager)
    );
  }
}