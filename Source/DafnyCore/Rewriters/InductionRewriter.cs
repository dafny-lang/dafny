using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class InductionRewriter : IRewriter {
  internal InductionRewriter(ErrorReporter reporter) : base(reporter) {
    Contract.Requires(reporter != null);
  }

  internal override void PostDecreasesResolve(ModuleDefinition m) {
    if (DafnyOptions.O.Induction == 0) {
      // Don't bother inferring :induction attributes.  This will also have the effect of not warning about malformed :induction attributes
    } else {
      foreach (var decl in m.TopLevelDecls) {
        if (decl is TopLevelDeclWithMembers) {
          var cl = (TopLevelDeclWithMembers)decl;
          foreach (var member in cl.Members) {
            if (member is ExtremeLemma) {
              var method = (ExtremeLemma)member;
              ProcessMethodExpressions(method);
              ComputeLemmaInduction(method.PrefixLemma);
              ProcessMethodExpressions(method.PrefixLemma);
            } else if (member is Method) {
              var method = (Method)member;
              ComputeLemmaInduction(method);
              ProcessMethodExpressions(method);
            } else if (member is ExtremePredicate) {
              var function = (ExtremePredicate)member;
              ProcessFunctionExpressions(function);
              ProcessFunctionExpressions(function.PrefixPredicate);
            } else if (member is Function) {
              var function = (Function)member;
              ProcessFunctionExpressions(function);
              if (function.ByMethodDecl != null) {
                ProcessMethodExpressions(function.ByMethodDecl);
              }
            }
          }
        }
        if (decl is NewtypeDecl) {
          var nt = (NewtypeDecl)decl;
          if (nt.Constraint != null) {
            var visitor = new Induction_Visitor(this);
            visitor.Visit(nt.Constraint);
          }
        }
      }
    }
  }

  void ProcessMethodExpressions(Method method) {
    Contract.Requires(method != null);
    var visitor = new Induction_Visitor(this);
    method.Req.ForEach(mfe => visitor.Visit(mfe.E));
    method.Ens.ForEach(mfe => visitor.Visit(mfe.E));
    if (method.Body != null) {
      visitor.Visit(method.Body);
    }
  }

  void ProcessFunctionExpressions(Function function) {
    Contract.Requires(function != null);
    var visitor = new Induction_Visitor(this);
    function.Req.ForEach(visitor.Visit);
    function.Ens.ForEach(visitor.Visit);
    if (function.Body != null) {
      visitor.Visit(function.Body);
    }
  }

  void ComputeLemmaInduction(Method method) {
    Contract.Requires(method != null);
    if (method.Body != null && method.IsGhost && method.Mod.Expressions.Count == 0 && method.Outs.Count == 0 && !(method is ExtremeLemma)) {
      var specs = new List<Expression>();
      method.Req.ForEach(mfe => specs.Add(mfe.E));
      method.Ens.ForEach(mfe => specs.Add(mfe.E));
      ComputeInductionVariables(method.tok, method.Ins, specs, method, ref method.Attributes);
    }
  }

  void ComputeInductionVariables<VarType>(IToken tok, List<VarType> boundVars, List<Expression> searchExprs, Method lemma, ref Attributes attributes) where VarType : class, IVariable {
    Contract.Requires(tok != null);
    Contract.Requires(boundVars != null);
    Contract.Requires(searchExprs != null);
    Contract.Requires(DafnyOptions.O.Induction != 0);

    var args = Attributes.FindExpressions(attributes, "induction");  // we only look at the first one we find, since it overrides any other ones
    if (args == null) {
      if (DafnyOptions.O.Induction < 2) {
        // No explicit induction variables and we're asked not to infer anything, so we're done
        return;
      } else if (DafnyOptions.O.Induction == 2 && lemma != null) {
        // We're asked to infer induction variables only for quantifiers, not for lemmas
        return;
      } else if (DafnyOptions.O.Induction == 4 && lemma == null) {
        // We're asked to infer induction variables only for lemmas, not for quantifiers
        return;
      }
      // GO INFER below (only select boundVars)
    } else if (args.Count == 0) {
      // {:induction} is treated the same as {:induction true}, which says to automatically infer induction variables
      // GO INFER below (all boundVars)
    } else if (args.Count == 1 && args[0] is LiteralExpr && ((LiteralExpr)args[0]).Value is bool) {
      // {:induction false} or {:induction true}
      if (!(bool)((LiteralExpr)args[0]).Value) {
        // we're told not to infer anything
        return;
      }
      // GO INFER below (all boundVars)
    } else {
      // Here, we're expecting the arguments to {:induction args} to be a sublist of "this;boundVars", where "this" is allowed only
      // if "lemma" denotes an instance lemma.
      var goodArguments = new List<Expression>();
      var i = lemma != null && !lemma.IsStatic ? -1 : 0;  // -1 says it's okay to see "this" or any other parameter; 0 <= i says it's okay to see parameter i or higher
      foreach (var arg in args) {
        var ie = arg.Resolved as IdentifierExpr;
        if (ie != null) {
          var j = boundVars.FindIndex(v => v == ie.Var);
          if (0 <= j && i <= j) {
            goodArguments.Add(ie);
            i = j + 1;
            continue;
          }
          if (0 <= j) {
            Reporter.Warning(MessageSource.Rewriter, arg.tok, "{0}s given as :induction arguments must be given in the same order as in the {1}; ignoring attribute",
              lemma != null ? "lemma parameter" : "bound variable", lemma != null ? "lemma" : "quantifier");
            return;
          }
          // fall through for j < 0
        } else if (lemma != null && arg.Resolved is ThisExpr) {
          if (i < 0) {
            goodArguments.Add(arg.Resolved);
            i = 0;
            continue;
          }
          Reporter.Warning(MessageSource.Rewriter, arg.tok, "lemma parameters given as :induction arguments must be given in the same order as in the lemma; ignoring attribute");
          return;
        }
        Reporter.Warning(MessageSource.Rewriter, arg.tok, "invalid :induction attribute argument; expected {0}{1}; ignoring attribute",
          i == 0 ? "'false' or 'true' or " : "",
          lemma != null ? "lemma parameter" : "bound variable");
        return;
      }
      // The argument list was legal, so let's use it for the _induction attribute
      attributes = new Attributes("_induction", goodArguments, attributes);
      return;
    }

    // Okay, here we go, coming up with good induction setting for the given situation
    var inductionVariables = new List<Expression>();
    if (lemma != null && !lemma.IsStatic) {
      if (args != null || searchExprs.Exists(expr => FreeVariablesUtil.ContainsFreeVariable(expr, true, null))) {
        inductionVariables.Add(new ThisExpr(lemma));
      }
    }
    foreach (IVariable n in boundVars) {
      if (!(n.Type.IsTypeParameter || n.Type.IsOpaqueType || n.Type.IsInternalTypeSynonym) && (args != null || searchExprs.Exists(expr => VarOccursInArgumentToRecursiveFunction(expr, n)))) {
        inductionVariables.Add(new IdentifierExpr(n.Tok, n));
      }
    }
    if (inductionVariables.Count != 0) {
      // We found something usable, so let's record that in an attribute
      attributes = new Attributes("_induction", inductionVariables, attributes);
      // And since we're inferring something, let's also report that in a hover text.
      var s = Printer.OneAttributeToString(attributes, "induction");
      if (lemma is PrefixLemma) {
        s = lemma.Name + " " + s;
      }
      Reporter.Info(MessageSource.Rewriter, tok, s);
    }
  }
  class Induction_Visitor : BottomUpVisitor {
    readonly InductionRewriter IndRewriter;
    public Induction_Visitor(InductionRewriter inductionRewriter) {
      Contract.Requires(inductionRewriter != null);
      IndRewriter = inductionRewriter;
    }
    protected override void VisitOneExpr(Expression expr) {
      var q = expr as QuantifierExpr;
      if (q != null && q.SplitQuantifier == null) {
        IndRewriter.ComputeInductionVariables(q.tok, q.BoundVars, new List<Expression>() { q.LogicalBody() }, null, ref q.Attributes);
      }
    }
  }

  /// <summary>
  /// Returns 'true' iff by looking at 'expr' the Induction Heuristic determines that induction should be applied to 'n'.
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
  public static bool VarOccursInArgumentToRecursiveFunction(Expression expr, IVariable n) {
    switch (DafnyOptions.O.InductionHeuristic) {
      case 0: return true;
      case 1: return FreeVariablesUtil.ContainsFreeVariable(expr, false, n);
      default: return VarOccursInArgumentToRecursiveFunction(expr, n, false);
    }
  }

  /// <summary>
  /// Worker routine for VarOccursInArgumentToRecursiveFunction(expr,n), where the additional parameter 'exprIsProminent' says whether or
  /// not 'expr' has prominent status in its context.
  /// DafnyInductionHeuristic cases 0 and 1 are assumed to be handled elsewhere (i.e., a precondition of this method is DafnyInductionHeuristic is at least 2).
  /// </summary>
  static bool VarOccursInArgumentToRecursiveFunction(Expression expr, IVariable n, bool exprIsProminent) {
    Contract.Requires(expr != null);
    Contract.Requires(n != null);

    // The following variable is what gets passed down to recursive calls if the subexpression does not itself acquire prominent status.
    var subExprIsProminent = DafnyOptions.O.InductionHeuristic == 2 || DafnyOptions.O.InductionHeuristic == 4 ? /*once prominent, always prominent*/exprIsProminent : /*reset the prominent status*/false;

    if (expr is IdentifierExpr) {
      var e = (IdentifierExpr)expr;
      return exprIsProminent && e.Var == n;
    } else if (expr is SeqSelectExpr) {
      var e = (SeqSelectExpr)expr;
      var q = DafnyOptions.O.InductionHeuristic < 4 || subExprIsProminent;
      return VarOccursInArgumentToRecursiveFunction(e.Seq, n, subExprIsProminent) ||  // this subexpression does not acquire "prominent" status
             (e.E0 != null && VarOccursInArgumentToRecursiveFunction(e.E0, n, q)) ||  // this one does (unless arrays/sequences are excluded)
             (e.E1 != null && VarOccursInArgumentToRecursiveFunction(e.E1, n, q));    // ditto
    } else if (expr is MultiSelectExpr) {
      var e = (MultiSelectExpr)expr;
      var q = DafnyOptions.O.InductionHeuristic < 4 || subExprIsProminent;
      return VarOccursInArgumentToRecursiveFunction(e.Array, n, subExprIsProminent) ||
             e.Indices.Exists(exp => VarOccursInArgumentToRecursiveFunction(exp, n, q));
    } else if (expr is FunctionCallExpr) {
      var e = (FunctionCallExpr)expr;
      // For recursive functions:  arguments are "prominent"
      // For non-recursive function:  arguments are "prominent" if the call is
      var rec = e.Function.IsRecursive && e.CoCall != FunctionCallExpr.CoCallResolution.Yes;
      var decr = e.Function.Decreases.Expressions;
      bool variantArgument;
      if (DafnyOptions.O.InductionHeuristic < 6) {
        variantArgument = rec;
      } else {
        // The receiver is considered to be "variant" if the function is recursive and the receiver participates
        // in the effective decreases clause of the function.  The receiver participates if it's a free variable
        // of a term in the explicit decreases clause.
        variantArgument = rec && decr.Exists(ee => FreeVariablesUtil.ContainsFreeVariable(ee, true, null));
      }
      if (VarOccursInArgumentToRecursiveFunction(e.Receiver, n, variantArgument || subExprIsProminent)) {
        return true;
      }
      Contract.Assert(e.Function.Formals.Count == e.Args.Count);
      for (int i = 0; i < e.Function.Formals.Count; i++) {
        var f = e.Function.Formals[i];
        var exp = e.Args[i];
        if (DafnyOptions.O.InductionHeuristic < 6) {
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
        if (VarOccursInArgumentToRecursiveFunction(exp, n, variantArgument || subExprIsProminent)) {
          return true;
        }
      }
      return false;
    } else if (expr is TernaryExpr) {
      var e = (TernaryExpr)expr;
      switch (e.Op) {
        case TernaryExpr.Opcode.PrefixEqOp:
        case TernaryExpr.Opcode.PrefixNeqOp:
          return VarOccursInArgumentToRecursiveFunction(e.E0, n, true) ||
                 VarOccursInArgumentToRecursiveFunction(e.E1, n, subExprIsProminent) ||
                 VarOccursInArgumentToRecursiveFunction(e.E2, n, subExprIsProminent);
        default:
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected ternary expression
      }
    } else if (expr is DatatypeValue) {
      var e = (DatatypeValue)expr;
      var q = n.Type.IsDatatype ? exprIsProminent : subExprIsProminent;  // prominent status continues, if we're looking for a variable whose type is a datatype
      return e.Arguments.Exists(exp => VarOccursInArgumentToRecursiveFunction(exp, n, q));
    } else if (expr is UnaryExpr) {
      var e = (UnaryExpr)expr;
      // both Not and SeqLength preserve prominence
      return VarOccursInArgumentToRecursiveFunction(e.E, n, exprIsProminent);
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
      return VarOccursInArgumentToRecursiveFunction(e.E0, n, q) ||
             VarOccursInArgumentToRecursiveFunction(e.E1, n, q);
    } else if (expr is StmtExpr) {
      var e = (StmtExpr)expr;
      // ignore the statement
      return VarOccursInArgumentToRecursiveFunction(e.E, n);

    } else if (expr is ITEExpr) {
      var e = (ITEExpr)expr;
      return VarOccursInArgumentToRecursiveFunction(e.Test, n, subExprIsProminent) ||  // test is not "prominent"
             VarOccursInArgumentToRecursiveFunction(e.Thn, n, exprIsProminent) ||  // but the two branches are
             VarOccursInArgumentToRecursiveFunction(e.Els, n, exprIsProminent);
    } else if (expr is OldExpr ||
               expr is ConcreteSyntaxExpression ||
               expr is BoxingCastExpr ||
               expr is UnboxingCastExpr) {
      foreach (var exp in expr.SubExpressions) {
        if (VarOccursInArgumentToRecursiveFunction(exp, n, exprIsProminent)) {  // maintain prominence
          return true;
        }
      }
      return false;
    } else {
      // in all other cases, reset the prominence status and recurse on the subexpressions
      foreach (var exp in expr.SubExpressions) {
        if (VarOccursInArgumentToRecursiveFunction(exp, n, subExprIsProminent)) {
          return true;
        }
      }
      return false;
    }
  }
}