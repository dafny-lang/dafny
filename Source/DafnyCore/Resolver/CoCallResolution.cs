using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

class CoCallResolution {
  readonly Function currentFunction;
  readonly bool dealsWithCodatatypes;
  public bool HasIntraClusterCallsInDestructiveContexts = false;
  public readonly List<CoCallInfo> FinalCandidates = [];

  public CoCallResolution(Function currentFunction, bool dealsWithCodatatypes) {
    Contract.Requires(currentFunction != null);
    this.currentFunction = currentFunction;
    this.dealsWithCodatatypes = dealsWithCodatatypes;
  }

  /// <summary>
  /// Determines which calls in "expr" can be considered to be co-calls, which co-constructor
  /// invocations host such co-calls, and which destructor operations are not allowed.
  /// Also records whether or not there are any intra-cluster calls in a destructive context.
  /// Assumes "expr" to have been successfully resolved.
  /// </summary>
  public void CheckCoCalls(Expression expr) {
    Contract.Requires(expr != null);
    CheckCoCalls(expr, 0, null, FinalCandidates);
  }

  public struct CoCallInfo {
    public readonly FunctionCallExpr CandidateCall;
    public readonly DatatypeValue EnclosingCoConstructor;
    public CoCallInfo(FunctionCallExpr candidateCall, DatatypeValue enclosingCoConstructor) {
      Contract.Requires(candidateCall != null);
      Contract.Requires(enclosingCoConstructor != null);
      CandidateCall = candidateCall;
      EnclosingCoConstructor = enclosingCoConstructor;
    }
  }

  /// <summary>
  /// Recursively goes through the entire "expr".  Every call within the same recursive cluster is a potential
  /// co-call.  If the call is determined not to be a co-recursive call, then its .CoCall field is filled in;
  /// if the situation deals with co-datatypes, then one of the NoBecause... values is chosen (rather
  /// than just No), so that any error message that may later be produced when trying to prove termination of the
  /// recursive call can include a note pointing out that the call was not selected to be a co-call.
  /// If the call looks like it is guarded, then it is added to the list "coCandicates", so that a later analysis
  /// can either set all of those .CoCall fields to Yes or to NoBecauseRecursiveCallsInDestructiveContext, depending
  /// on other intra-cluster calls.
  /// The "destructionLevel" indicates how many pending co-destructors the context has.  It may be infinity (int.MaxValue)
  /// if the enclosing context has no easy way of controlling the uses of "expr" (for example, if the enclosing context
  /// passes "expr" to a function or binds "expr" to a variable).  It is never negative -- excess co-constructors are
  /// not considered an asset, and any immediately enclosing co-constructor is passed in as a non-null "coContext" anyway.
  /// "coContext" is non-null if the immediate context is a co-constructor.
  /// </summary>
  void CheckCoCalls(Expression expr, int destructionLevel, DatatypeValue coContext, List<CoCallInfo> coCandidates, Function functionYouMayWishWereAbstemious = null) {
    Contract.Requires(expr != null);

    Contract.Requires(0 <= destructionLevel);
    Contract.Requires(coCandidates != null);
    expr = expr.Resolved;
    if (expr is DatatypeValue) {
      var e = (DatatypeValue)expr;
      if (e.Ctor.EnclosingDatatype is CoDatatypeDecl) {
        int dl = destructionLevel == int.MaxValue ? int.MaxValue : destructionLevel == 0 ? 0 : destructionLevel - 1;
        foreach (var arg in e.Arguments) {
          CheckCoCalls(arg, dl, e, coCandidates);
        }
        return;
      }
    } else if (expr is MemberSelectExpr) {
      var e = (MemberSelectExpr)expr;
      if (e.Member.EnclosingClass is CoDatatypeDecl) {
        int dl = destructionLevel == int.MaxValue ? int.MaxValue : destructionLevel + 1;
        CheckCoCalls(e.Obj, dl, coContext, coCandidates);
        return;
      }
    } else if (expr is BinaryExpr) {
      var e = (BinaryExpr)expr;
      if (e.ResolvedOp == BinaryExpr.ResolvedOpcode.EqCommon || e.ResolvedOp == BinaryExpr.ResolvedOpcode.NeqCommon) {
        // Equality and disequality (for any type that may contain a co-datatype) are as destructive as can be--in essence,
        // they destruct the values indefinitely--so don't allow any co-recursive calls in the operands.
        CheckCoCalls(e.E0, int.MaxValue, null, coCandidates);
        CheckCoCalls(e.E1, int.MaxValue, null, coCandidates);
        return;
      }
    } else if (expr is TernaryExpr) {
      var e = (TernaryExpr)expr;
      if (e.Op == TernaryExpr.Opcode.PrefixEqOp || e.Op == TernaryExpr.Opcode.PrefixNeqOp) {
        // Prefix equality and disequality (for any type that may contain a co-datatype) are destructive.
        CheckCoCalls(e.E0, int.MaxValue, null, coCandidates);
        CheckCoCalls(e.E1, int.MaxValue, null, coCandidates);
        CheckCoCalls(e.E2, int.MaxValue, null, coCandidates);
        return;
      }
    } else if (expr is NestedMatchExpr) {
      var e = (NestedMatchExpr)expr;
      foreach (var child in e.SubExpressions) {
        CheckCoCalls(child, destructionLevel, coContext, coCandidates);
      }
    } else if (expr is MatchExpr) {
      var e = (MatchExpr)expr;
      CheckCoCalls(e.Source, int.MaxValue, null, coCandidates);
      foreach (var kase in e.Cases) {
        CheckCoCalls(kase.Body, destructionLevel, coContext, coCandidates);
      }
      return;
    } else if (expr is ITEExpr) {
      var e = (ITEExpr)expr;
      CheckCoCalls(e.Test, int.MaxValue, null, coCandidates);
      CheckCoCalls(e.Thn, destructionLevel, coContext, coCandidates);
      CheckCoCalls(e.Els, destructionLevel, coContext, coCandidates);
      return;
    } else if (expr is FunctionCallExpr) {
      var e = (FunctionCallExpr)expr;
      // First, consider the arguments of the call, making sure that they do not include calls within the recursive cluster,
      // unless the callee is abstemious.
      var abstemious = true;
      if (!Attributes.ContainsBool(e.Function.Attributes, "abstemious", ref abstemious)) {
        abstemious = false;
      }
      Contract.Assert(e.Args.Count == e.Function.Ins.Count);
      for (var i = 0; i < e.Args.Count; i++) {
        var arg = e.Args[i];
        if (!e.Function.Ins[i].Type.IsCoDatatype) {
          CheckCoCalls(arg, int.MaxValue, null, coCandidates);
        } else if (abstemious) {
          CheckCoCalls(arg, 0, coContext, coCandidates);
        } else {
          // don't you wish the callee were abstemious
          CheckCoCalls(arg, int.MaxValue, null, coCandidates, e.Function);
        }
      }
      // Second, investigate the possibility that this call itself may be a candidate co-call
      if (e.Name != "requires" && ModuleDefinition.InSameSCC(currentFunction, e.Function)) {
        // This call goes to another function in the same recursive cluster
        if (destructionLevel != 0 && GuaranteedCoCtors(e.Function) <= destructionLevel) {
          // a potentially destructive context
          HasIntraClusterCallsInDestructiveContexts = true;  // this says we found an intra-cluster call unsuitable for recursion, if there were any co-recursive calls
          if (!dealsWithCodatatypes) {
            e.CoCall = FunctionCallExpr.CoCallResolution.No;
          } else {
            e.CoCall = FunctionCallExpr.CoCallResolution.NoBecauseRecursiveCallsAreNotAllowedInThisContext;
            if (functionYouMayWishWereAbstemious != null) {
              e.CoCallHint = string.Format("perhaps try declaring function '{0}' with '{{:abstemious}}'", functionYouMayWishWereAbstemious.Name);
            }
          }
        } else if (coContext == null) {
          // no immediately enclosing co-constructor
          if (!dealsWithCodatatypes) {
            e.CoCall = FunctionCallExpr.CoCallResolution.No;
          } else {
            e.CoCall = FunctionCallExpr.CoCallResolution.NoBecauseIsNotGuarded;
          }
        } else if (e.Function.Reads.Expressions.Count != 0) {
          // this call is disqualified from being a co-call, because of side effects
          if (!dealsWithCodatatypes) {
            e.CoCall = FunctionCallExpr.CoCallResolution.No;
          } else {
            e.CoCall = FunctionCallExpr.CoCallResolution.NoBecauseFunctionHasSideEffects;
          }
        } else if (e.Function.Ens.Count != 0) {
          // this call is disqualified from being a co-call, because it has a postcondition
          // (a postcondition could be allowed, as long as it does not get to be used with
          // co-recursive calls, because that could be unsound; for example, consider
          // "ensures false")
          if (!dealsWithCodatatypes) {
            e.CoCall = FunctionCallExpr.CoCallResolution.No;
          } else {
            e.CoCall = FunctionCallExpr.CoCallResolution.NoBecauseFunctionHasPostcondition;
          }
        } else {
          // e.CoCall is not filled in here, but will be filled in when the list of candidates are processed
          coCandidates.Add(new CoCallInfo(e, coContext));
        }
      }
      return;
    } else if (expr is LambdaExpr) {
      var e = (LambdaExpr)expr;
      CheckCoCalls(e.Term, destructionLevel, coContext, coCandidates);
      if (e.Range != null) {
        CheckCoCalls(e.Range, int.MaxValue, null, coCandidates);
      }
      foreach (var read in e.Reads.Expressions) {
        CheckCoCalls(read.E, int.MaxValue, null, coCandidates);
      }
      return;
    } else if (expr is MapComprehension) {
      var e = (MapComprehension)expr;
      foreach (var ee in Attributes.SubExpressions(e.Attributes)) {
        CheckCoCalls(ee, int.MaxValue, null, coCandidates);
      }
      if (e.Range != null) {
        CheckCoCalls(e.Range, int.MaxValue, null, coCandidates);
      }
      // allow co-calls in the term
      if (e.TermLeft != null) {
        CheckCoCalls(e.TermLeft, destructionLevel, coContext, coCandidates);
      }
      CheckCoCalls(e.Term, destructionLevel, coContext, coCandidates);
      return;
    } else if (expr is OldExpr) {
      var e = (OldExpr)expr;
      // here, "coContext" is passed along (the use of "old" says this must be ghost code, so the compiler does not need to handle this case)
      CheckCoCalls(e.Expr, destructionLevel, coContext, coCandidates);
      return;
    } else if (expr is LetExpr) {
      var e = (LetExpr)expr;
      foreach (var rhs in e.RHSs) {
        CheckCoCalls(rhs, int.MaxValue, null, coCandidates);
      }
      CheckCoCalls(e.Body, destructionLevel, coContext, coCandidates);
      return;
    } else if (expr is ApplyExpr) {
      var e = (ApplyExpr)expr;
      CheckCoCalls(e.Function, int.MaxValue, null, coCandidates);
      foreach (var ee in e.Args) {
        CheckCoCalls(ee, destructionLevel, null, coCandidates);
      }
      return;
    }

    // Default handling:
    foreach (var ee in expr.SubExpressions) {
      CheckCoCalls(ee, destructionLevel, null, coCandidates);
    }
  }

  public static int GuaranteedCoCtors(Function function) {
    Contract.Requires(function != null);
    return function.Body != null ? GuaranteedCoCtorsAux(function.Body) : 0;
  }

  private static int GuaranteedCoCtorsAux(Expression expr) {
    Contract.Requires(expr != null);
    expr = expr.Resolved;
    if (expr is DatatypeValue) {
      var e = (DatatypeValue)expr;
      if (e.Ctor.EnclosingDatatype is CoDatatypeDecl) {
        var minOfArgs = int.MaxValue;  // int.MaxValue means: not yet encountered a formal whose type is a co-datatype
        Contract.Assert(e.Arguments.Count == e.Ctor.Formals.Count);
        for (var i = 0; i < e.Arguments.Count; i++) {
          if (e.Ctor.Formals[i].Type.IsCoDatatype) {
            var n = GuaranteedCoCtorsAux(e.Arguments[i]);
            minOfArgs = Math.Min(minOfArgs, n);
          }
        }
        return minOfArgs == int.MaxValue ? 1 : 1 + minOfArgs;
      }
    } else if (expr is ITEExpr) {
      var e = (ITEExpr)expr;
      var thn = GuaranteedCoCtorsAux(e.Thn);
      var els = GuaranteedCoCtorsAux(e.Els);
      return thn < els ? thn : els;
    } else if (expr is NestedMatchExpr nestedMatchExpr) {
      var childValues = nestedMatchExpr.Cases.Select(child => GuaranteedCoCtorsAux(child.Body)).ToList();
      return childValues.Any() ? childValues.Min() : 0;
    } else if (expr is MatchExpr) {
      var e = (MatchExpr)expr;
      var min = int.MaxValue;
      foreach (var kase in e.Cases) {
        var n = GuaranteedCoCtorsAux(kase.Body);
        min = Math.Min(min, n);
      }
      return min == int.MaxValue ? 0 : min;
    } else if (expr is LetExpr) {
      var e = (LetExpr)expr;
      return GuaranteedCoCtorsAux(e.Body);
    } else if (expr is IdentifierExpr) {
      var e = (IdentifierExpr)expr;
      if (e.Type.IsCoDatatype && e.Var is Formal) {
        // even though this is not a co-constructor, count this as 1, since that's what we would have done if it were, e.g., "Cons(s.head, s.tail)" instead of "s"
        return 1;
      }
    }
    return 0;
  }
}