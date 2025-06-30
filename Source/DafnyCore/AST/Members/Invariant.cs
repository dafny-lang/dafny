using System.Collections.Generic;
using System.Linq;
using JetBrains.Annotations;

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
  public readonly List<AttributedExpression> Clauses = clauses;
  public Expression ResolvedCall(IOrigin origin, Expression receiver, SystemModuleManager systemModuleManager) =>
    Expression.CreateResolvedCall(origin, receiver, this, [], [], systemModuleManager);
}