using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using JetBrains.Annotations;

namespace Microsoft.Dafny;

public class ExpressionTester {
  private bool ReportErrors => reporter != null;
  [CanBeNull] private readonly ErrorReporter reporter; // if null, no errors will be reported

  /// <summary>
  /// If "resolver" is non-null, CheckIsCompilable will update some fields in the resolver. In particular,
  ///   - .InCompiledContext in DatatypeUpdateExpr will be updated
  ///   - for a FunctionCallExpr that calls a function-by-method in a compiled context, a call-graph edge will be
  ///     added from the caller to the by-method.
  ///   - .Constraint_Bounds of LetExpr will be updated
  /// </summary>
  [CanBeNull] private readonly Resolver resolver; // if non-null, CheckIsCompilable will update some fields in the resolver

  private ExpressionTester([CanBeNull] Resolver resolver, [CanBeNull] ErrorReporter reporter) {
    this.resolver = resolver;
    this.reporter = reporter;
  }

  // Static call to CheckIsCompilable
  public static bool CheckIsCompilable([CanBeNull] Resolver resolver, Expression expr, ICodeContext codeContext) {
    return new ExpressionTester(resolver, resolver?.Reporter).CheckIsCompilable(expr, codeContext);
  }
  // Static call to CheckIsCompilable
  public static bool CheckIsCompilable(Resolver resolver, ErrorReporter reporter, Expression expr, ICodeContext codeContext) {
    return new ExpressionTester(resolver, reporter).CheckIsCompilable(expr, codeContext);
  }

  /// <summary>
  /// Checks that "expr" is compilable and reports an error if it is not.
  /// Also, updates bookkeeping information for the verifier to record the fact that "expr" is to be compiled.
  /// For example, this bookkeeping information keeps track of if the constraint of a let-such-that expression
  /// must determine the value uniquely.
  /// Requires "expr" to have been successfully resolved.
  /// </summary>
  private bool CheckIsCompilable(Expression expr, ICodeContext codeContext) {
    Contract.Requires(expr != null);
    Contract.Requires(expr.WasResolved());  // this check approximates the requirement that "expr" be resolved
    Contract.Requires(codeContext != null || reporter == null);

    var isCompilable = true;

    if (expr is IdentifierExpr expression) {
      if (expression.Var != null && expression.Var.IsGhost) {
        reporter?.Error(MessageSource.Resolver, expression,
          $"ghost variables such as {expression.Name} are allowed only in specification contexts. {expression.Name} was inferred to be ghost based on its declaration or initialization.");
        return false;
      }

    } else if (expr is MemberSelectExpr selectExpr) {
      if (reporter != null) {
        selectExpr.InCompiledContext = true;
      }
      if (selectExpr.Member != null && selectExpr.Member.IsGhost) {
        var what = selectExpr.Member.WhatKindMentionGhost;
        reporter?.Error(MessageSource.Resolver, selectExpr, $"a {what} is allowed only in specification contexts");
        return false;
      } else if (selectExpr.Member is Function function && function.Formals.Any(formal => formal.IsGhost)) {
        var what = selectExpr.Member.WhatKindMentionGhost;
        reporter?.Error(MessageSource.Resolver, selectExpr, $"a {what} with ghost parameters can be used as a value only in specification contexts");
        return false;
      } else if (selectExpr.Member is DatatypeDestructor dtor && dtor.EnclosingCtors.All(ctor => ctor.IsGhost)) {
        var what = selectExpr.Member.WhatKind;
        reporter?.Error(MessageSource.Resolver, selectExpr, $"{what} '{selectExpr.MemberName}' can be used only in specification contexts");
        return false;
      }

    } else if (expr is DatatypeUpdateExpr updateExpr) {
      if (resolver != null) {
        updateExpr.InCompiledContext = true;
      }
      isCompilable = CheckIsCompilable(updateExpr.Root, codeContext);
      Contract.Assert(updateExpr.Members.Count == updateExpr.Updates.Count);
      for (var i = 0; i < updateExpr.Updates.Count; i++) {
        var member = (DatatypeDestructor)updateExpr.Members[i];
        if (!member.IsGhost) {
          isCompilable = CheckIsCompilable(updateExpr.Updates[i].Item3, codeContext) && isCompilable;
        }
      }
      if (updateExpr.LegalSourceConstructors.All(ctor => ctor.IsGhost)) {
        var dtors = Util.PrintableNameList(updateExpr.Members.ConvertAll(dtor => dtor.Name), "and");
        var ctorNames = DatatypeDestructor.PrintableCtorNameList(updateExpr.LegalSourceConstructors, "or");
        reporter?.Error(MessageSource.Resolver, updateExpr,
          $"in a compiled context, update of {dtors} cannot be applied to a datatype value of a ghost variant (ghost constructor {ctorNames})");
        isCompilable = false;
      }
      // switch to the desugared expression for compiled contexts, but don't step into it
      updateExpr.ResolvedExpression = updateExpr.ResolvedCompiledExpression;
      return isCompilable;

    } else if (expr is FunctionCallExpr callExpr) {
      if (callExpr.Function != null) {
        if (callExpr.Function.IsGhost) {
          if (ReportErrors == false) {
            return false;
          }

          string msg;
          if (callExpr.Function is TwoStateFunction || callExpr.Function is ExtremePredicate || callExpr.Function is PrefixPredicate) {
            msg = $"a call to a {callExpr.Function.WhatKind} is allowed only in specification contexts";
          } else {
            var what = callExpr.Function.WhatKind;
            string compiledDeclHint;
            if (DafnyOptions.O.FunctionSyntax == FunctionSyntaxOptions.Version4) {
              compiledDeclHint = "without the 'ghost' keyword";
            } else {
              compiledDeclHint = $"with '{what} method'";
            }
            msg = $"a call to a ghost {what} is allowed only in specification contexts (consider declaring the {what} {compiledDeclHint})";
          }
          reporter?.Error(MessageSource.Resolver, callExpr, msg);
          return false;
        }
        if (callExpr.Function.ByMethodBody != null) {
          Contract.Assert(callExpr.Function.ByMethodDecl != null); // we expect .ByMethodDecl to have been filled in by now
          // this call will really go to the method part of the function-by-method, so add that edge to the call graph
          if (resolver != null) {
            CallGraphBuilder.AddCallGraphEdge(codeContext, callExpr.Function.ByMethodDecl, callExpr, reporter);
          }
          callExpr.IsByMethodCall = true;
        }
        // function is okay, so check all NON-ghost arguments
        isCompilable = CheckIsCompilable(callExpr.Receiver, codeContext);
        for (var i = 0; i < callExpr.Function.Formals.Count; i++) {
          if (!callExpr.Function.Formals[i].IsGhost && i < callExpr.Args.Count) {
            isCompilable = CheckIsCompilable(callExpr.Args[i], codeContext) && isCompilable;
          }
        }
      }

      return isCompilable;

    } else if (expr is DatatypeValue value) {
      if (value.Ctor.IsGhost) {
        reporter?.Error(MessageSource.Resolver, expr, "ghost constructor is allowed only in specification contexts");
        isCompilable = false;
      }
      // check all NON-ghost arguments
      // note that if resolution is successful, then |e.Arguments| == |e.Ctor.Formals|
      for (int i = 0; i < value.Arguments.Count; i++) {
        if (!value.Ctor.Formals[i].IsGhost) {
          isCompilable = CheckIsCompilable(value.Arguments[i], codeContext) && isCompilable;
        }
      }
      return isCompilable;

    } else if (expr is OldExpr) {
      reporter?.Error(MessageSource.Resolver, expr, "old expressions are allowed only in specification and ghost contexts");
      return false;

    } else if (expr is TypeTestExpr tte) {
      if (!IsTypeTestCompilable(tte)) {
        reporter?.Error(MessageSource.Resolver, tte, $"an expression of type '{tte.E.Type}' is not run-time checkable to be a '{tte.ToType}'");
        return false;
      }

    } else if (expr is FreshExpr) {
      reporter?.Error(MessageSource.Resolver, expr, "fresh expressions are allowed only in specification and ghost contexts");
      return false;

    } else if (expr is UnchangedExpr) {
      reporter?.Error(MessageSource.Resolver, expr, "unchanged expressions are allowed only in specification and ghost contexts");
      return false;

    } else if (expr is StmtExpr stmtExpr) {
      // ignore the statement
      return CheckIsCompilable(stmtExpr.E, codeContext);

    } else if (expr is BinaryExpr binaryExpr) {
      if (reporter != null) {
        binaryExpr.InCompiledContext = true;
      }
      switch (binaryExpr.ResolvedOp_PossiblyStillUndetermined) {
        case BinaryExpr.ResolvedOpcode.RankGt:
        case BinaryExpr.ResolvedOpcode.RankLt:
          reporter?.Error(MessageSource.Resolver, binaryExpr, "rank comparisons are allowed only in specification and ghost contexts");
          return false;
      }
    } else if (expr is TernaryExpr ternaryExpr) {
      switch (ternaryExpr.Op) {
        case TernaryExpr.Opcode.PrefixEqOp:
        case TernaryExpr.Opcode.PrefixNeqOp:
          reporter?.Error(MessageSource.Resolver, ternaryExpr, "prefix equalities are allowed only in specification and ghost contexts");
          return false;
      }
    } else if (expr is LetExpr letExpr) {
      if (letExpr.Exact) {
        Contract.Assert(letExpr.LHSs.Count == letExpr.RHSs.Count);
        var i = 0;
        foreach (var ee in letExpr.RHSs) {
          var lhs = letExpr.LHSs[i];
          // Make LHS vars ghost if the RHS is a ghost
          if (UsesSpecFeatures(ee)) {
            foreach (var bv in lhs.Vars) {
              if (!bv.IsGhost) {
                bv.MakeGhost();
                isCompilable = false;
              }
            }
          }

          if (!lhs.Vars.All(bv => bv.IsGhost)) {
            isCompilable = CheckIsCompilable(ee, codeContext) && isCompilable;
          }
          i++;
        }
        isCompilable = CheckIsCompilable(letExpr.Body, codeContext) && isCompilable;
      } else {
        Contract.Assert(letExpr.RHSs.Count == 1);
        var lhsVarsAreAllGhost = letExpr.BoundVars.All(bv => bv.IsGhost);
        if (!lhsVarsAreAllGhost) {
          isCompilable = CheckIsCompilable(letExpr.RHSs[0], codeContext) && isCompilable;
        }
        isCompilable = CheckIsCompilable(letExpr.Body, codeContext) && isCompilable;

        // fill in bounds for this to-be-compiled let-such-that expression
        Contract.Assert(letExpr.RHSs.Count == 1);  // if we got this far, the resolver will have checked this condition successfully
        var constraint = letExpr.RHSs[0];
        if (resolver != null) {
          letExpr.Constraint_Bounds = Resolver.DiscoverBestBounds_MultipleVars(letExpr.BoundVars.ToList<IVariable>(),
            constraint, true, ComprehensionExpr.BoundedPool.PoolVirtues.None);
        }
      }
      return isCompilable;
    } else if (expr is LambdaExpr lambdaExpr) {
      return CheckIsCompilable(lambdaExpr.Body, codeContext);
    } else if (expr is ComprehensionExpr comprehensionExpr) {
      var uncompilableBoundVars = comprehensionExpr.UncompilableBoundVars();
      if (uncompilableBoundVars.Count != 0) {
        string what;
        if (comprehensionExpr is SetComprehension comprehension) {
          what = comprehension.Finite ? "set comprehensions" : "iset comprehensions";
        } else if (comprehensionExpr is MapComprehension mapComprehension) {
          what = mapComprehension.Finite ? "map comprehensions" : "imap comprehensions";
        } else {
          Contract.Assume(comprehensionExpr is QuantifierExpr);  // otherwise, unexpected ComprehensionExpr (since LambdaExpr is handled separately above)
          Contract.Assert(((QuantifierExpr)comprehensionExpr).SplitQuantifier == null); // No split quantifiers during resolution
          what = "quantifiers";
        }
        foreach (var bv in uncompilableBoundVars) {
          reporter?.Error(MessageSource.Resolver, comprehensionExpr,
            $"{what} in non-ghost contexts must be compilable, but Dafny's heuristics can't figure out how to produce or compile a bounded set of values for '{bv.Name}'");
          isCompilable = false;
        }
      }
      // don't recurse down any attributes
      if (comprehensionExpr.Range != null) {
        isCompilable = CheckIsCompilable(comprehensionExpr.Range, codeContext) && isCompilable;
      }
      isCompilable = CheckIsCompilable(comprehensionExpr.Term, codeContext) && isCompilable;
      return isCompilable;

    } else if (expr is ChainingExpression chainingExpression) {
      // We don't care about the different operators; we only want the operands, so let's get them directly from
      // the chaining expression
      return chainingExpression.Operands.TrueForAll(ee => CheckIsCompilable(ee, codeContext));

    } else if (expr is MatchExpr matchExpr) {
      var mc = FirstCaseThatDependsOnGhostCtor(matchExpr.Cases);
      if (mc != null) {
        reporter?.Error(MessageSource.Resolver, mc.tok, "match expression is not compilable, because it depends on a ghost constructor");
        isCompilable = false;
      }
      // other conditions are checked below
    }

    foreach (var ee in expr.SubExpressions) {
      isCompilable = CheckIsCompilable(ee, codeContext) && isCompilable;
    }

    return isCompilable;
  }


  public static bool IsTypeTestCompilable(TypeTestExpr tte) {
    Contract.Requires(tte != null);
    var fromType = tte.E.Type;
    if (fromType.IsSubtypeOf(tte.ToType, false, true)) {
      // this is a no-op, so it can trivially be compiled
      return true;
    }

    // TODO: It would be nice to allow some subset types in test tests in compiled code. But for now, such cases
    // are allowed only in ghost contexts.
    var udtTo = (UserDefinedType)tte.ToType.NormalizeExpandKeepConstraints();
    if (udtTo.ResolvedClass is SubsetTypeDecl && !(udtTo.ResolvedClass is NonNullTypeDecl)) {
      return false;
    }

    // The operation can be performed at run time if the mapping of .ToType's type parameters are injective in fromType's type parameters.
    // For illustration, suppose the "is"-operation is testing whether or not the given expression of type A<X> has type B<Y>, where
    // X and Y are some type expressions. At run time, we can check if the expression has type B<...>, but we can't on all target platforms
    // be certain about the "...". So, if both B<Y> and B<Y'> are possible subtypes of A<X>, we can't perform the type test at run time.
    // In other words, we CAN perform the type test at run time if the type parameters of A uniquely determine the type parameters of B.
    // Let T be a list of type parameters (in particular, we will use the formal TypeParameter's declared in type B). Then, represent
    // B<T> in parent type A, and let's say the result is A<U> for some type expression U. If U contains all type parameters from T,
    // then the mapping from B<T> to A<U> is unique, which means the mapping frmo B<Y> to A<X> is unique, which means we can check if an
    // A<X> value is a B<Y> value by checking if the value is of type B<...>.
    var B = ((UserDefinedType)tte.ToType.NormalizeExpandKeepConstraints()).ResolvedClass; // important to keep constraints here, so no type parameters are lost
    var B_T = UserDefinedType.FromTopLevelDecl(tte.tok, B);
    var tps = new HashSet<TypeParameter>(); // There are going to be the type parameters of fromType (that is, T in the discussion above)
    if (fromType.TypeArgs.Count != 0) {
      // we need this "if" statement, because if "fromType" is "object" or "object?", then it isn't a UserDefinedType
      var A = (UserDefinedType)fromType.NormalizeExpand(); // important to NOT keep constraints here, since they won't be evident at run time
      var A_U = B_T.AsParentType(A.ResolvedClass);
      // the type test can be performed at run time if all the type parameters of "B_T" are free type parameters of "A_U".
      A_U.AddFreeTypeParameters(tps);
    }
    foreach (var tp in B.TypeArgs) {
      if (!tps.Contains(tp)) {
        // type test cannot be performed at run time, so this is a ghost operation
        // TODO: If "tp" is a type parameter for which there is a run-time type descriptor, then we would still be able to perform
        // the type test at run time.
        return false;
      }
    }
    // type test can be performed at run time
    return true;
  }

  /// <summary>
  /// Returns whether or not 'expr' has any subexpression that uses some feature (like a ghost or quantifier)
  /// that is allowed only in specification contexts.
  /// Requires 'expr' to be a successfully resolved expression.
  ///
  /// Note, some expressions have different proof obligations in ghost and compiled contexts. For example,
  /// a let-such-that expression in a compiled context is required to have a uniquely determined result.
  /// For such an expression, "UsesSpecFeatures" returns "false", since the feature can be used in either ghost
  /// or compiled contexts. Whenever "UsesSpecFeatures" returns "false", the caller has a choice about making
  /// the expression ghost or making it compiled. If the caller chooses to make the expression compiled, the
  /// caller must then call "CheckIsCompilable" to commit this choice, because "CheckIsCompilable" fills in
  /// various bookkeeping information that the verifier will need.
  /// </summary>
  public static bool UsesSpecFeatures(Expression expr) {
    Contract.Requires(expr != null);
    Contract.Requires(expr.WasResolved());  // this check approximates the requirement that "expr" be resolved

    if (expr is LiteralExpr) {
      return false;
    } else if (expr is ThisExpr) {
      return false;
    } else if (expr is IdentifierExpr) {
      IdentifierExpr e = (IdentifierExpr)expr;
      return cce.NonNull(e.Var).IsGhost;
    } else if (expr is DatatypeValue) {
      var e = (DatatypeValue)expr;
      if (e.Ctor.IsGhost) {
        return true;
      }

      // check all NON-ghost arguments
      // note that if resolution is successful, then |e.Arguments| == |e.Ctor.Formals|
      for (int i = 0; i < e.Arguments.Count; i++) {
        if (!e.Ctor.Formals[i].IsGhost && UsesSpecFeatures(e.Arguments[i])) {
          return true;
        }
      }
      return false;
    } else if (expr is DisplayExpression) {
      DisplayExpression e = (DisplayExpression)expr;
      return e.Elements.Exists(ee => UsesSpecFeatures(ee));
    } else if (expr is MapDisplayExpr) {
      MapDisplayExpr e = (MapDisplayExpr)expr;
      return e.Elements.Exists(p => UsesSpecFeatures(p.A) || UsesSpecFeatures(p.B));
    } else if (expr is MemberSelectExpr) {
      var e = (MemberSelectExpr)expr;
      if (UsesSpecFeatures(e.Obj)) {
        return true;
      } else if (e.Member != null && e.Member.IsGhost) {
        return true;
      } else if (e.Member is Function function && function.Formals.Any(formal => formal.IsGhost)) {
        return true;
      } else if (e.Member is DatatypeDestructor dtor) {
        return dtor.EnclosingCtors.All(ctor => ctor.IsGhost);
      } else {
        return false;
      }
    } else if (expr is DatatypeUpdateExpr updateExpr) {
      if (UsesSpecFeatures(updateExpr.Root)) {
        return true;
      }
      Contract.Assert(updateExpr.Members.Count == updateExpr.Updates.Count);
      for (var i = 0; i < updateExpr.Updates.Count; i++) {
        var member = (DatatypeDestructor)updateExpr.Members[i];
        // note, updating a ghost field does not make the expression ghost (cf. ghost let expressions)
        if (!member.IsGhost && UsesSpecFeatures(updateExpr.Updates[i].Item3)) {
          return true;
        }
      }
      return updateExpr.LegalSourceConstructors.All(ctor => ctor.IsGhost);

    } else if (expr is SeqSelectExpr) {
      SeqSelectExpr e = (SeqSelectExpr)expr;
      return UsesSpecFeatures(e.Seq) ||
             (e.E0 != null && UsesSpecFeatures(e.E0)) ||
             (e.E1 != null && UsesSpecFeatures(e.E1));
    } else if (expr is MultiSelectExpr) {
      MultiSelectExpr e = (MultiSelectExpr)expr;
      return UsesSpecFeatures(e.Array) || e.Indices.Exists(ee => UsesSpecFeatures(ee));
    } else if (expr is SeqUpdateExpr) {
      SeqUpdateExpr e = (SeqUpdateExpr)expr;
      return UsesSpecFeatures(e.Seq) ||
             UsesSpecFeatures(e.Index) ||
             UsesSpecFeatures(e.Value);
    } else if (expr is FunctionCallExpr) {
      var e = (FunctionCallExpr)expr;
      if (e.Function.IsGhost) {
        return true;
      }
      // check all NON-ghost arguments
      if (UsesSpecFeatures(e.Receiver)) {
        return true;
      }
      for (int i = 0; i < e.Function.Formals.Count; i++) {
        if (!e.Function.Formals[i].IsGhost && UsesSpecFeatures(e.Args[i])) {
          return true;
        }
      }
      return false;
    } else if (expr is ApplyExpr) {
      ApplyExpr e = (ApplyExpr)expr;
      return UsesSpecFeatures(e.Function) || e.Args.Exists(UsesSpecFeatures);
    } else if (expr is OldExpr || expr is UnchangedExpr) {
      return true;
    } else if (expr is UnaryExpr) {
      var e = (UnaryExpr)expr;
      if (e is UnaryOpExpr { Op: UnaryOpExpr.Opcode.Fresh or UnaryOpExpr.Opcode.Allocated }) {
        return true;
      }
      if (expr is TypeTestExpr tte && !IsTypeTestCompilable(tte)) {
        return true;
      }
      return UsesSpecFeatures(e.E);
    } else if (expr is BinaryExpr) {
      BinaryExpr e = (BinaryExpr)expr;
      switch (e.ResolvedOp_PossiblyStillUndetermined) {
        case BinaryExpr.ResolvedOpcode.RankGt:
        case BinaryExpr.ResolvedOpcode.RankLt:
          return true;
        default:
          return UsesSpecFeatures(e.E0) || UsesSpecFeatures(e.E1);
      }
    } else if (expr is TernaryExpr) {
      var e = (TernaryExpr)expr;
      switch (e.Op) {
        case TernaryExpr.Opcode.PrefixEqOp:
        case TernaryExpr.Opcode.PrefixNeqOp:
          return true;
        default:
          break;
      }
      return UsesSpecFeatures(e.E0) || UsesSpecFeatures(e.E1) || UsesSpecFeatures(e.E2);
    } else if (expr is LetExpr) {
      var e = (LetExpr)expr;
      if (e.Exact) {
        MakeGhostAsNeeded(e.LHSs);
        return UsesSpecFeatures(e.Body);
      } else {
        Contract.Assert(e.RHSs.Count == 1);
        if (UsesSpecFeatures(e.RHSs[0])) {
          foreach (var bv in e.BoundVars) {
            bv.MakeGhost();
          }
        }
        return UsesSpecFeatures(e.Body);
      }
    } else if (expr is QuantifierExpr) {
      var e = (QuantifierExpr)expr;
      if (e.SplitQuantifier != null) {
        return UsesSpecFeatures(e.SplitQuantifierExpression);
      }
      return e.UncompilableBoundVars().Count != 0 || UsesSpecFeatures(e.LogicalBody());
    } else if (expr is SetComprehension) {
      var e = (SetComprehension)expr;
      return !e.Finite || e.UncompilableBoundVars().Count != 0 || (e.Range != null && UsesSpecFeatures(e.Range)) || (e.Term != null && UsesSpecFeatures(e.Term));
    } else if (expr is MapComprehension) {
      var e = (MapComprehension)expr;
      return !e.Finite || e.UncompilableBoundVars().Count != 0 || UsesSpecFeatures(e.Range) || (e.TermLeft != null && UsesSpecFeatures(e.TermLeft)) || UsesSpecFeatures(e.Term);
    } else if (expr is LambdaExpr) {
      var e = (LambdaExpr)expr;
      return UsesSpecFeatures(e.Term);
    } else if (expr is WildcardExpr) {
      return false;
    } else if (expr is StmtExpr) {
      var e = (StmtExpr)expr;
      return UsesSpecFeatures(e.E);
    } else if (expr is ITEExpr) {
      ITEExpr e = (ITEExpr)expr;
      return UsesSpecFeatures(e.Test) || UsesSpecFeatures(e.Thn) || UsesSpecFeatures(e.Els);
    } else if (expr is NestedMatchExpr nestedMatchExpr) {
      return nestedMatchExpr.Cases.SelectMany(caze => caze.Pat.DescendantsAndSelf.OfType<IdPattern>().Where(id => id.Ctor != null)).Any(id => id.Ctor.IsGhost)
             || expr.SubExpressions.Any(child => UsesSpecFeatures(child));
    } else if (expr is MatchExpr) {
      MatchExpr me = (MatchExpr)expr;
      if (UsesSpecFeatures(me.Source) || FirstCaseThatDependsOnGhostCtor(me.Cases) != null) {
        return true;
      }
      return me.Cases.Exists(mc => UsesSpecFeatures(mc.Body));
    } else if (expr is ConcreteSyntaxExpression) {
      var e = (ConcreteSyntaxExpression)expr;
      return e.ResolvedExpression != null && UsesSpecFeatures(e.ResolvedExpression);
    } else if (expr is SeqConstructionExpr) {
      var e = (SeqConstructionExpr)expr;
      return UsesSpecFeatures(e.N) || UsesSpecFeatures(e.Initializer);
    } else if (expr is MultiSetFormingExpr) {
      var e = (MultiSetFormingExpr)expr;
      return UsesSpecFeatures(e.E);
    } else {
      Contract.Assert(false); throw new cce.UnreachableException();  // unexpected expression
    }
  }
  static void MakeGhostAsNeeded(List<CasePattern<BoundVar>> lhss) {
    foreach (CasePattern<BoundVar> lhs in lhss) {
      MakeGhostAsNeeded(lhs);
    }
  }

  static void MakeGhostAsNeeded(CasePattern<BoundVar> lhs) {
    if (lhs.Ctor != null && lhs.Arguments != null) {
      for (int i = 0; i < lhs.Arguments.Count && i < lhs.Ctor.Destructors.Count; i++) {
        MakeGhostAsNeeded(lhs.Arguments[i], lhs.Ctor.Destructors[i]);
      }
    }
  }

  static void MakeGhostAsNeeded(CasePattern<BoundVar> arg, DatatypeDestructor d) {
    if (arg.Expr is IdentifierExpr ie && ie.Var is BoundVar bv) {
      if (d.IsGhost) {
        bv.MakeGhost();
      }
    }
    if (arg.Ctor != null) {
      MakeGhostAsNeeded(arg);
    }
  }

  /// <summary>
  /// Return the first ghost constructor listed in a case, or null, if there is none.
  /// </summary>
  public static MC FirstCaseThatDependsOnGhostCtor<MC>(List<MC> cases) where MC : MatchCase {
    return cases.FirstOrDefault(kees => kees.Ctor.IsGhost, null);
  }
}
