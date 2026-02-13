using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using JetBrains.Annotations;
using static Microsoft.Dafny.ResolutionErrors;

namespace Microsoft.Dafny;

public class ExpressionTester {
  private readonly DafnyOptions options;
  private bool ReportErrors => reporter != null;
  [CanBeNull] private readonly ErrorReporter reporter; // if null, no errors will be reported

  /// <summary>
  /// If "resolver" is non-null, CheckIsCompilable will update some fields in the resolver. In particular,
  ///   - .InCompiledContext in DatatypeUpdateExpr will be updated
  ///   - for a FunctionCallExpr that calls a function-by-method in a compiled context, a call-graph edge will be
  ///     added from the caller to the by-method.
  ///   - .Constraint_Bounds of LetExpr will be updated
  /// </summary>
  [CanBeNull] private readonly ModuleResolver resolver; // if non-null, CheckIsCompilable will update some fields in the resolver

  private ExpressionTester([CanBeNull] ModuleResolver resolver, [CanBeNull] ErrorReporter reporter, DafnyOptions options) {
    this.resolver = resolver;
    this.reporter = reporter;
    this.options = options;
  }

  /// <summary>
  /// Determines whether or not "expr" is compilable, and returns the answer.
  /// If "resolver" is non-null and "expr" is not compilable, then an error is reported.
  /// Also, updates various bookkeeping information (see instance method CheckIsCompilable for more details).
  /// </summary>
  public static bool CheckIsCompilable(DafnyOptions options, [CanBeNull] ModuleResolver resolver, Expression expr, ICodeContext codeContext) {
    return new ExpressionTester(resolver, resolver?.Reporter, options).CheckIsCompilable(expr, codeContext, true);
  }

  /// <summary>
  /// Checks that "expr" is compilable and report an error if it is not.
  /// Also, updates various bookkeeping information (see instance method CheckIsCompilable for more details).
  /// </summary>
  public static void CheckIsCompilable(ModuleResolver resolver, ErrorReporter reporter, Expression expr, ICodeContext codeContext) {
    new ExpressionTester(resolver, reporter, reporter.Options).CheckIsCompilable(expr, codeContext, true);
  }

  private void ReportError(ErrorId errorId, Expression e, params object[] messageParts) {
    reporter?.Error(MessageSource.Resolver, errorId, e, messageParts);
  }

  private void ReportError(ErrorId errorId, IOrigin t, params object[] messageParts) {
    reporter?.Error(MessageSource.Resolver, errorId, t, messageParts);
  }

  /// <summary>
  /// Determines and returns whether or not "expr" is compilable.
  /// If it is not, it calls ReportError. (Note, whether or not ReportError reports an error depends on if "reporter" is non-null.)
  ///
  /// Also, updates bookkeeping information for the verifier to record the fact that "expr" is to be compiled.
  /// For example, this bookkeeping information keeps track of if the constraint of a let-such-that expression
  /// must determine the value uniquely.
  /// Requires "expr" to have been successfully resolved.
  ///
  /// An expression is considered to be "insideBranchesOnly" if the enclosing context consists only of "if"
  /// conditions that decide whether or not to return the value of this expression. For example, if the
  /// expression
  ///     if E then F else 2 + G
  /// is considered "insideBranchesOnly", then so if "F", but not "E" or "G".
  /// </summary>
  private bool CheckIsCompilable(Expression expr, ICodeContext codeContext, bool insideBranchesOnly = false) {
    Contract.Requires(expr != null);
    Contract.Requires(expr.WasResolved());  // this check approximates the requirement that "expr" be resolved
    Contract.Requires(codeContext != null || reporter == null);

    var isCompilable = true;
    // The subexpressions of "if" and "match" essentially consist of a "condition" and some "branches".
    // The branches inherit the "insideBranchesOnly" value, but the condition does not. To code this without
    // copying what the .SubExpression getter does for "if" and "match", the local variable
    // "subexpressionsAreInsideBranchesOnlyExcept". If it is non-null, "expr" is of the condition/branches variety
    // "subexpressionsAreInsideBranchesOnlyExcept" is its condition.
    Expression subexpressionsAreInsideBranchesOnlyExcept = null;

    if (expr is IdentifierExpr expression) {
      if (expression.Var is { IsGhost: true }) {
        ReportError(ErrorId.r_ghost_var_only_in_specifications, expression,
          $"ghost variables such as {expression.Name} are allowed only in specification contexts. {expression.Name} was inferred to be ghost based on its declaration or initialization.");
        return false;
      }

    } else if (expr is MemberSelectExpr selectExpr) {
      if (reporter != null) {
        selectExpr.InCompiledContext = true;
      }
      if (selectExpr.Member != null && selectExpr.Member.IsGhost) {
        var what = selectExpr.Member.WhatKindMentionGhost;
        ReportError(ErrorId.r_only_in_specification, selectExpr, $"a {what} is allowed only in specification contexts");
        return false;
      } else if (selectExpr.Member is Function function && function.Ins.Any(formal => formal.IsGhost)) {
        var what = selectExpr.Member.WhatKindMentionGhost;
        ReportError(ErrorId.r_ghost_parameters_only_in_specification, selectExpr, $"a {what} with ghost parameters can be used as a value only in specification contexts");
        return false;
      } else if (selectExpr.Member is DatatypeDestructor dtor && dtor.EnclosingCtors.All(ctor => ctor.IsGhost)) {
        var what = selectExpr.Member.WhatKind;
        ReportError(ErrorId.r_used_only_in_specification, selectExpr, $"{what} '{selectExpr.MemberName}' can be used only in specification contexts");
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
        ReportError(ErrorId.r_ghost_destructor_update_not_compilable, updateExpr,
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
          ErrorId errorId;
          if (callExpr.Function is TwoStateFunction || callExpr.Function is ExtremePredicate || callExpr.Function is PrefixPredicate) {
            msg = $"a call to a {callExpr.Function.WhatKind} is allowed only in specification contexts";
            errorId = ErrorId.r_ghost_call_only_in_specification;
          } else {
            var what = callExpr.Function.WhatKind;
            string compiledDeclHint;
            if (options.FunctionSyntax == FunctionSyntaxOptions.Version4) {
              compiledDeclHint = "without the 'ghost' keyword";
              errorId = ErrorId.r_ghost_call_only_in_specification_function_4;
            } else {
              compiledDeclHint = $"with '{what} method'";
              errorId = ErrorId.r_ghost_call_only_in_specification_function_3;
            }
            msg = $"a call to a ghost {what} is allowed only in specification contexts (consider declaring the {what} {compiledDeclHint})";
          }
          ReportError(errorId, callExpr, msg);
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
        for (var i = 0; i < callExpr.Function.Ins.Count; i++) {
          if (!callExpr.Function.Ins[i].IsGhost && i < callExpr.Args.Count) {
            isCompilable = CheckIsCompilable(callExpr.Args[i], codeContext) && isCompilable;
          }
        }
      }

      return isCompilable;

    } else if (expr is DatatypeValue value) {
      if (value.Ctor.IsGhost) {
        ReportError(ErrorId.r_ghost_constructors_only_in_ghost_context, expr, "ghost constructor is allowed only in specification contexts");
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
      ReportError(ErrorId.r_old_expressions_only_in_ghost_context, expr, "old expressions are allowed only in specification and ghost contexts");
      return false;

    } else if (expr is TypeTestExpr tte) {
      if (!IsTypeTestCompilable(tte)) {
        ReportError(ErrorId.r_type_test_not_runtime_checkable, tte, $"an expression of type '{tte.E.Type}' is not run-time checkable to be a '{tte.ToType}'");
        return false;
      }

    } else if (expr is FreshExpr) {
      ReportError(ErrorId.r_fresh_expressions_only_in_ghost_context, expr, "fresh expressions are allowed only in specification and ghost contexts");
      return false;

    } else if (expr is UnchangedExpr) {
      ReportError(ErrorId.r_unchanged_expressions_only_in_ghost_context, expr, "unchanged expressions are allowed only in specification and ghost contexts");
      return false;

    } else if (expr is StmtExpr stmtExpr) {
      // ignore the statement
      return CheckIsCompilable(stmtExpr.E, codeContext, insideBranchesOnly);

    } else if (expr is BinaryExpr binaryExpr) {
      if (reporter != null) {
        binaryExpr.InCompiledContext = true;
      }
      switch (binaryExpr.ResolvedOp_PossiblyStillUndetermined) {
        case BinaryExpr.ResolvedOpcode.RankGt:
        case BinaryExpr.ResolvedOpcode.RankLt:
          ReportError(ErrorId.r_rank_expressions_only_in_ghost_context, binaryExpr, "rank comparisons are allowed only in specification and ghost contexts");
          return false;
      }
    } else if (expr is TernaryExpr ternaryExpr) {
      switch (ternaryExpr.Op) {
        case TernaryExpr.Opcode.PrefixEqOp:
        case TernaryExpr.Opcode.PrefixNeqOp:
          ReportError(ErrorId.r_prefix_equalities_only_in_ghost_context, ternaryExpr, "prefix equalities are allowed only in specification and ghost contexts");
          return false;
      }
    } else if (expr is LetExpr letExpr) {
      if (letExpr.Exact) {
        Contract.Assert(letExpr.LHSs.Count == letExpr.RHSs.Count);
        for (var i = 0; i < letExpr.RHSs.Count; i++) {
          var rhs = letExpr.RHSs[i];
          var lhs = letExpr.LHSs[i];
          // Make LHS vars ghost if the RHS is a ghost
          if (UsesSpecFeatures(rhs)) {
            foreach (var bv in lhs.Vars) {
              if (!bv.IsGhost) {
                bv.MakeGhost();
              }
            }
          }

          if (!lhs.Vars.All(bv => bv.IsGhost)) {
            isCompilable = CheckIsCompilable(rhs, codeContext) && isCompilable;
          }
        }
        isCompilable = CheckIsCompilable(letExpr.Body, codeContext, insideBranchesOnly) && isCompilable;
      } else {
        Contract.Assert(letExpr.RHSs.Count == 1);
        var lhsVarsAreAllGhost = letExpr.BoundVars.All(bv => bv.IsGhost);
        if (!lhsVarsAreAllGhost) {
          isCompilable = CheckIsCompilable(letExpr.RHSs[0], codeContext) && isCompilable;
        }
        isCompilable = CheckIsCompilable(letExpr.Body, codeContext, insideBranchesOnly) && isCompilable;

        // fill in bounds for this to-be-compiled let-such-that expression
        Contract.Assert(letExpr.RHSs.Count == 1); // if we got this far, the resolver will have checked this condition successfully
        var constraint = letExpr.RHSs[0];
        if (resolver != null) {
          letExpr.Constraint_Bounds = ModuleResolver.DiscoverBestBounds_MultipleVars(letExpr.BoundVars.ToList<IVariable>(), constraint, true);
        }
      }
      return isCompilable;

    } else if (expr is NestedMatchExpr nestedMatchExpr) {
      foreach (var kase in nestedMatchExpr.Cases) {
        MakeGhostAsNeeded(kase.Pat, false);
      }

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
          ReportError(ErrorId.r_unknown_bounds, comprehensionExpr,
            $"{what} in non-ghost contexts must be compilable, but Dafny's heuristics can't figure out how to produce or compile a bounded set of values for '{bv.Name}'");
          isCompilable = false;
        }
      }
      // don't recurse down any attributes
      if (comprehensionExpr.Range != null) {
        isCompilable = CheckIsCompilable(comprehensionExpr.Range, codeContext) && isCompilable;
      }
      if (comprehensionExpr is MapComprehension { TermLeft: { } termLeft }) {
        isCompilable = CheckIsCompilable(termLeft, codeContext) && isCompilable;
      }
      isCompilable = CheckIsCompilable(comprehensionExpr.Term, codeContext) && isCompilable;
      return isCompilable;

    } else if (expr is ChainingExpression chainingExpression) {
      // We don't care about the different operators; we only want the operands, so let's get them directly from
      // the chaining expression
      return chainingExpression.Operands.TrueForAll(ee => CheckIsCompilable(ee, codeContext));

    } else if (expr is ITEExpr iteExpr) {
      // An if-then-else expression is compilable if its guard, then branch, and else branch all are.
      // But there's another situation when it's compilable, namely when the enclosing context is a
      // compiled function, say F(x, ghost y) where parameters x are compiled and parameters y are ghost,
      // and one of the branches of the if-then-else expression ends with a recursive call F(s, t)
      // where the actual parameters s are exactly the formal parameters x. In that case, the way to
      // compile the if-then-else expression is to ignore the test expression and the branch that
      // ends as just described, and instead just compile the other branch.
      if (codeContext is Function function && insideBranchesOnly) {
        bool onlyGhostParametersChange(Expression ee) {
          if (ee is FunctionCallExpr functionCallExpr && functionCallExpr.Function == function) {
            if (!function.IsStatic && functionCallExpr.Receiver.Resolved is not ThisExpr) {
              return false;
            }
            Contract.Assert(function.Ins.Count == functionCallExpr.Args.Count);
            for (var i = 0; i < function.Ins.Count; i++) {
              var formal = function.Ins[i];
              if (!formal.IsGhost && !IdentifierExpr.Is(functionCallExpr.Args[i], formal)) {
                return false;
              }
            }
            return true;
          }
          return false;
        }

        if (iteExpr.Thn.TerminalExpressions.All(onlyGhostParametersChange)) {
          // mark "else" branch as the one to compile
          iteExpr.HowToCompile = ITEExpr.ITECompilation.CompileJustElseBranch;
          return CheckIsCompilable(iteExpr.Els, codeContext, insideBranchesOnly);
        } else if (iteExpr.Els.TerminalExpressions.All(onlyGhostParametersChange)) {
          // mark "then" branch as the one to compile
          iteExpr.HowToCompile = ITEExpr.ITECompilation.CompileJustThenBranch;
          return CheckIsCompilable(iteExpr.Thn, codeContext, insideBranchesOnly);
        }
      }
      subexpressionsAreInsideBranchesOnlyExcept = iteExpr.Test;

    } else if (expr is MatchExpr matchExpr) {
      var mc = FirstCaseThatDependsOnGhostCtor(matchExpr.Cases);
      if (mc != null) {
        ReportError(ErrorId.r_match_not_compilable, mc.Origin, "match expression is not compilable, because it depends on a ghost constructor");
        isCompilable = false;
      }
      // other conditions are checked below
      subexpressionsAreInsideBranchesOnlyExcept = matchExpr.Source;

    } else if (expr is DecreasesToExpr _) {
      ReportError(ErrorId.r_decreases_to_only_in_specification,
                  expr, "a `decreases to` expression is allowed only in specification and ghost contexts");
      return false;

    } else if (expr is ConcreteSyntaxExpression { ResolvedExpression: not null } concreteSyntaxExpression) {
      return CheckIsCompilable(concreteSyntaxExpression.ResolvedExpression, codeContext, insideBranchesOnly);
    }

    foreach (var ee in expr.SubExpressions) {
      var eeIsOnlyInsideBranches = insideBranchesOnly && subexpressionsAreInsideBranchesOnlyExcept != null && subexpressionsAreInsideBranchesOnlyExcept != ee;
      isCompilable = CheckIsCompilable(ee, codeContext, eeIsOnlyInsideBranches) && isCompilable;
    }

    return isCompilable;
  }

  public static bool IsTypeTestCompilable(TypeTestExpr tte) {
    return IsTypeTestCompilable(tte.E.Type, tte.ToType);
  }

  /// <summary>
  /// This method determines if it's possible, at run time, to test if something whose static type is "fromType"
  /// is of type "toType". This information is need for "is" expressions and comprehension expressions. By the
  /// time that this method is called, it has already been determined that the use is legal by the type system;
  /// this method performs the additional check of compilability, which is needed in non-ghost contexts.
  ///
  /// What this method does falls into three parts:
  ///
  /// 0. If "toType" is a supertype of "fromType", then a type test would always return "true". A similar situation
  /// is when "toType" is a non-null type and the nullable version of "toType" is a supertype of "from"; then,
  /// the run-time type tests consists simply of a non-null check. Else, if "toType" is a type parameter, then we
  /// never allow the check in compiled code.
  ///
  /// If those simple cases don't apply, there the compilability of the type test comes down to two remaining parts:
  ///
  /// 1. If "toType" is a subset type or newtype that involves constraints, then those constraints have to be compilable.
  /// (Actually, this could be improved in a future version of Dafny, because we're given that any constraints of
  /// "fromType" already hold. Thus, we really just need to check that the constraints _between_ "fromType" and "toType"
  /// are compilable.)
  ///
  /// 2. The third part is to check that "toType" is injective in its type parameters. That is, we want to check that the
  /// type arguments of "toType" are uniquely determined from the type arguments of "fromType".
  /// To illustrate the need for this injectivity check, suppose the "is"-operation is testing whether or not the given expression
  /// of type A<X> has type B<Y>, where X and Y are some type expressions. If the type parameterization Y is uniquely determined
  /// from X, then all we need to check at run time is whether or not the A thing is a B thing. (This happens to be supported in all
  /// our target languages, even those target languages that do not themselves have full support for type parameters.)
  /// On the other hand, if there are several ways to parameterize B to make it be comparable to A<X> (say, B<Y> and B<Z>), then
  /// a type test like this would at run time recover some information about the type arguments. This goes against the principle of
  /// "parametric polymorphism", which in essence says that once types are passed in as type parameters, there's no way at run time
  /// to figure out what they are.
  /// Now, even if you think that insisting on parametric polymorphism is taking the high road to language design and that parametric
  /// polymorphism has no tangible benefits, the injectivity rule still makes sense for Dafny. This is because type parameters in the
  /// Dafny target code are more coarse-grained than the Dafny type parameters. For example, we don't distinguish "int" and "nat" in
  /// the target code. In fact, some of our target languages either don't support type parameters at all (like in Go) or don't give us
  /// a way to check them at run time (like in Java). So, even without the lofty goal of parametric polymorphism, we'd be out of luck
  /// trying to distinguish B<Y> from B<Z> at run time.
  /// </summary>
  public static bool IsTypeTestCompilable(Type fromType, Type toType) {
    // part 0
    if (fromType.IsSubtypeOf(toType, false, true)) {
      // this requires no run-time work or a simple null comparison, so it can trivially be compiled
      return true;
    }
    if (toType.IsTypeParameter) {
      // this is never allowed in compiled code
      return false;
    }

    // part 1
    if (toType.NormalizeExpandKeepConstraints() is UserDefinedType { ResolvedClass: RedirectingTypeDecl { ConstraintIsCompilable: false } }) {
      // the constraint can't be evaluated at run time, so the type test cannot be compiled
      return false;
    }

    // part 2
    if (toType.NormalizeExpandKeepConstraints() is UserDefinedType udtTo) {
      // check that "udtTo" is injective in its type parameters

      // Suppose "fromType" is A<...> and that "udtTo" is B<...>. Let T be a list of type parameters (in particular, we will use the formal
      // TypeParameter's declared in type B). To perform the injectivity check, we first represent B<T> in parent type A (typically by
      // calling "AsParentType"). Let's say the result is A<U> for some type expression U. If U contains all type parameters from T, then the
      // mapping from B<T> to A<U> is unique, which means the mapping from B<Y> to A<X> is unique.
      var B = udtTo.ResolvedClass;
      var B_T = UserDefinedType.FromTopLevelDecl(B.Origin, B);

      var A = fromType.NormalizeExpand(); // important to NOT keep constraints here, since they won't be evident at run time
      Type A_U;
      if (A is UserDefinedType udtA) {
        A_U = B_T.AsParentType(udtA.ResolvedClass);
      } else {
        // Evidently, A is not a newtype, subset type, (co)datatype, abstract type, reference type, or trait type (except possibly "object?"). Hence:
        Contract.Assert(A.NormalizeToAncestorType().Equals(A));
        // We can therefore move B_T up to its parent A by normalizing, expanding, and trimming it all the way.
        A_U = B_T.NormalizeToAncestorType();
      }

      // the type test can be performed at run time if all the type parameters of "B_T" are free type parameters of "A_U".
      var tps = new HashSet<TypeParameter>();
      A_U.AddFreeTypeParameters(tps);
      if (B.TypeArgs.Any(tp => !tps.Contains(tp))) {
        // type test cannot be performed at run time, so this is a ghost operation
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
      return Cce.NonNull(e.Var).IsGhost;
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
      } else if (e.Member is Function function && function.Ins.Any(formal => formal.IsGhost)) {
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
      for (int i = 0; i < e.Function.Ins.Count; i++) {
        if (!e.Function.Ins[i].IsGhost && UsesSpecFeatures(e.Args[i])) {
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
      if (e is UnaryOpExpr { Op: UnaryOpExpr.Opcode.Fresh or UnaryOpExpr.Opcode.Allocated or UnaryOpExpr.Opcode.Assigned }) {
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
      return e.UncompilableBoundVars().Count != 0 || (e.Range != null && UsesSpecFeatures(e.Range)) || (e.Term != null && UsesSpecFeatures(e.Term));
    } else if (expr is MapComprehension) {
      var e = (MapComprehension)expr;
      return e.UncompilableBoundVars().Count != 0 || UsesSpecFeatures(e.Range) || (e.TermLeft != null && UsesSpecFeatures(e.TermLeft)) || UsesSpecFeatures(e.Term);
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
    } else if (expr is IndexFieldLocation or FieldLocation) {
      return true;
    } else if (expr is LocalsObjectExpression) {
      return true;
    } else {
      Contract.Assert(false); throw new Cce.UnreachableException();  // unexpected expression
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

  public static void MakeGhostAsNeeded(ExtendedPattern extendedPattern, bool inGhostContext) {
    if (extendedPattern is DisjunctivePattern disjunctivePattern) {
      foreach (var alternative in disjunctivePattern.Alternatives) {
        MakeGhostAsNeeded(alternative, inGhostContext);
      }
    } else if (extendedPattern is LitPattern) {
      // nothing to do
    } else if (extendedPattern is IdPattern idPattern) {
      if (idPattern.BoundVar != null) {
        if (inGhostContext && !idPattern.BoundVar.IsGhost) {
          idPattern.BoundVar.MakeGhost();
        }
      } else if (idPattern.Ctor != null) {
        var argumentCount = idPattern.Ctor.Formals.Count;
        Contract.Assert(argumentCount == (idPattern.Arguments?.Count ?? 0));
        for (var i = 0; i < argumentCount; i++) {
          MakeGhostAsNeeded(idPattern.Arguments[i], inGhostContext || idPattern.Ctor.Formals[i].IsGhost);
        }
      }
    } else {
      Contract.Assert(false); // unexpected ExtendedPattern
    }
  }

  /// <summary>
  /// Return the first ghost constructor listed in a case, or null, if there is none.
  /// </summary>
  public static MC FirstCaseThatDependsOnGhostCtor<MC>(List<MC> cases) where MC : MatchCase {
    return cases.FirstOrDefault(kees => kees.Ctor.IsGhost, null);
  }
}
