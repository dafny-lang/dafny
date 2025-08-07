#nullable enable
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public static class InductionHeuristic {

  /// <summary>
  /// Returns 'true' iff by looking at 'expr' the Induction Heuristic determines that induction should be applied to 'n'.
  /// Variable 'n' can be passed in as 'null', in which case it stands for 'this'.
  /// 
  /// More precisely:
  ///   DafnyInductionHeuristic      Return 'true'
  ///   -----------------------      -------------
  ///        0                       always
  ///        1    if 'n' occurs as   any subexpression (of 'expr')
  ///        2    if 'n' occurs as   any subexpression of          any index argument of an array/sequence select expression or any                       argument to a recursive function
  ///        3    if 'n' occurs as   a prominent subexpression of  any index argument of an array/sequence select expression or any                       argument to a recursive function
  ///        4    if 'n' occurs as   any subexpression of                                                                       any                       argument to a recursive function
  ///        5    if 'n' occurs as   a prominent subexpression of                                                               any                       argument to a recursive function
  ///        6    if 'n' occurs as   a prominent subexpression of                                                               any decreases-influencing argument to a recursive function
  /// </summary>
  public static bool VarOccursInArgumentToRecursiveFunction(DafnyOptions options, Expression expr, IVariable? n) {
    switch (options.InductionHeuristic) {
      case 0: return true;
      case 1: return FreeVariablesUtil.ContainsFreeVariable(expr, n == null, n);
      default: return VarOccursInArgumentToRecursiveFunction(options, expr, n, false);
    }
  }

  /// <summary>
  /// Worker routine for VarOccursInArgumentToRecursiveFunction(expr,n), where the additional parameter 'exprIsProminent' says whether or
  /// not 'expr' has prominent status in its context.
  /// DafnyInductionHeuristic cases 0 and 1 are assumed to be handled elsewhere (i.e., a precondition of this method is DafnyInductionHeuristic is at least 2).
  /// Variable 'n' can be passed in as 'null', in which case it stands for 'this'.
  /// </summary>
  static bool VarOccursInArgumentToRecursiveFunction(DafnyOptions options, Expression expr, IVariable? n, bool exprIsProminent) {
    Contract.Requires(expr != null);
    Contract.Requires(n != null);

    // The following variable is what gets passed down to recursive calls if the subexpression does not itself acquire prominent status.
    var subExprIsProminent = options.InductionHeuristic == 2 || options.InductionHeuristic == 4 ? /*once prominent, always prominent*/exprIsProminent : /*reset the prominent status*/false;

    if (n != null && expr is IdentifierExpr) {
      var e = (IdentifierExpr)expr;
      return exprIsProminent && e.Var == n;
    } else if (n == null && expr is ThisExpr) {
      return exprIsProminent;
    } else if (expr is SeqSelectExpr) {
      var e = (SeqSelectExpr)expr;
      var q = options.InductionHeuristic < 4 || subExprIsProminent;
      return VarOccursInArgumentToRecursiveFunction(options, e.Seq, n, subExprIsProminent) ||  // this subexpression does not acquire "prominent" status
        (e.E0 != null && VarOccursInArgumentToRecursiveFunction(options, e.E0, n, q)) ||  // this one does (unless arrays/sequences are excluded)
        (e.E1 != null && VarOccursInArgumentToRecursiveFunction(options, e.E1, n, q));    // ditto
    } else if (expr is MultiSelectExpr) {
      var e = (MultiSelectExpr)expr;
      var q = options.InductionHeuristic < 4 || subExprIsProminent;
      return VarOccursInArgumentToRecursiveFunction(options, e.Array, n, subExprIsProminent) ||
        e.Indices.Exists(exp => VarOccursInArgumentToRecursiveFunction(options, exp, n, q));
    } else if (expr is FunctionCallExpr) {
      var e = (FunctionCallExpr)expr;
      // For recursive functions:  arguments are "prominent"
      // For non-recursive function:  arguments are "prominent" if the call is
      var rec = e.Function.IsRecursive && e.CoCall != FunctionCallExpr.CoCallResolution.Yes;
      var decr = e.Function.Decreases.Expressions!;
      bool variantArgument;
      if (options.InductionHeuristic < 6) {
        variantArgument = rec;
      } else {
        // The receiver is considered to be "variant" if the function is recursive and the receiver participates
        // in the effective decreases clause of the function.  The receiver participates if it's a free variable
        // of a term in the explicit decreases clause.
        variantArgument = rec && decr.Exists(ee => FreeVariablesUtil.ContainsFreeVariable(ee, true, null));
      }
      if (VarOccursInArgumentToRecursiveFunction(options, e.Receiver, n, variantArgument || subExprIsProminent)) {
        return true;
      }
      Contract.Assert(e.Function.Ins.Count == e.Args.Count);
      for (int i = 0; i < e.Function.Ins.Count; i++) {
        var f = e.Function.Ins[i];
        var exp = e.Args[i];
        if (options.InductionHeuristic < 6) {
          variantArgument = rec;
        } else if (rec) {
          // The argument position is considered to be "variant" if the function is recursive and...
          // ... it has something to do with why the callee is well-founded, which happens when...
          if (f is ImplicitFormal) {
            // ... it is the argument is the implicit _k parameter, which is always first in the effective decreases clause of a prefix lemma, or
            variantArgument = true;
          } else if (decr.Exists(ee => FreeVariablesUtil.ContainsFreeVariable(ee, false, f))) {
            // ... it participates in the effective decreases clause of the function, which happens when it is
            // a free variable of a term in the explicit decreases clause, or
            variantArgument = true;
          } else {
            // ... the callee is a prefix predicate.
            variantArgument = true;
          }
        }
        if (VarOccursInArgumentToRecursiveFunction(options, exp, n, variantArgument || subExprIsProminent)) {
          return true;
        }
      }
      return false;
    } else if (expr is TernaryExpr) {
      var e = (TernaryExpr)expr;
      switch (e.Op) {
        case TernaryExpr.Opcode.PrefixEqOp:
        case TernaryExpr.Opcode.PrefixNeqOp:
          return VarOccursInArgumentToRecursiveFunction(options, e.E0, n, true) ||
            VarOccursInArgumentToRecursiveFunction(options, e.E1, n, subExprIsProminent) ||
            VarOccursInArgumentToRecursiveFunction(options, e.E2, n, subExprIsProminent);
        default:
          Contract.Assert(false); throw new Cce.UnreachableException();  // unexpected ternary expression
      }
    } else if (expr is DatatypeValue value) {
      var q = n != null && n.Type.IsDatatype ? exprIsProminent : subExprIsProminent;  // prominent status continues, if we're looking for a variable whose type is a datatype
      return value.Arguments.Exists(exp => VarOccursInArgumentToRecursiveFunction(options, exp, n, q));
    } else if (expr is UnaryExpr) {
      var e = (UnaryExpr)expr;
      // both Not and SeqLength preserve prominence
      return VarOccursInArgumentToRecursiveFunction(options, e.E, n, exprIsProminent);
    } else if (expr is BinaryExpr) {
      var e = (BinaryExpr)expr;
      bool q;
      switch (e.ResolvedOp) {
        case BinaryExpr.ResolvedOpcode.Add:
        case BinaryExpr.ResolvedOpcode.Sub:
        case BinaryExpr.ResolvedOpcode.Mul:
        case BinaryExpr.ResolvedOpcode.Div:
        case BinaryExpr.ResolvedOpcode.Mod:
        case BinaryExpr.ResolvedOpcode.LeftShift:
        case BinaryExpr.ResolvedOpcode.RightShift:
        case BinaryExpr.ResolvedOpcode.BitwiseAnd:
        case BinaryExpr.ResolvedOpcode.BitwiseOr:
        case BinaryExpr.ResolvedOpcode.BitwiseXor:
        case BinaryExpr.ResolvedOpcode.Union:
        case BinaryExpr.ResolvedOpcode.Intersection:
        case BinaryExpr.ResolvedOpcode.SetDifference:
        case BinaryExpr.ResolvedOpcode.Concat:
          // these operators preserve prominence
          q = exprIsProminent;
          break;
        default:
          // whereas all other binary operators do not
          q = subExprIsProminent;
          break;
      }
      return VarOccursInArgumentToRecursiveFunction(options, e.E0, n, q) ||
        VarOccursInArgumentToRecursiveFunction(options, e.E1, n, q);
    } else if (expr is StmtExpr) {
      var e = (StmtExpr)expr;
      // ignore the statement
      return VarOccursInArgumentToRecursiveFunction(options, e.E, n, exprIsProminent);

    } else if (expr is ITEExpr) {
      var e = (ITEExpr)expr;
      return VarOccursInArgumentToRecursiveFunction(options, e.Test, n, subExprIsProminent) ||  // test is not "prominent"
        VarOccursInArgumentToRecursiveFunction(options, e.Thn, n, exprIsProminent) ||  // but the two branches are
        VarOccursInArgumentToRecursiveFunction(options, e.Els, n, exprIsProminent);
    } else if (expr is OldExpr ||
               expr is ConcreteSyntaxExpression ||
               expr is BoxingCastExpr ||
               expr is UnboxingCastExpr) {
      foreach (var exp in expr.SubExpressions) {
        if (VarOccursInArgumentToRecursiveFunction(options, exp, n, exprIsProminent)) {  // maintain prominence
          return true;
        }
      }
      return false;
    } else {
      // in all other cases, reset the prominence status and recurse on the subexpressions
      foreach (var exp in expr!.SubExpressions) {
        if (VarOccursInArgumentToRecursiveFunction(options, exp, n, subExprIsProminent)) {
          return true;
        }
      }
      return false;
    }
  }
}
