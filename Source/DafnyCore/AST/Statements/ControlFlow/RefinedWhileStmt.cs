using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

/// <summary>
/// This class is really just a WhileStmt, except that it serves the purpose of remembering if the object was created as the result of a refinement
/// merge.
/// </summary>
public class RefinedWhileStmt : WhileStmt {
  public RefinedWhileStmt(IOrigin rangeOrigin, Expression guard,
    List<AttributedExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod,
    BlockStmt body)
    : base(rangeOrigin, guard, invariants, decreases, mod, body) {
    Contract.Requires(body != null);
  }
}