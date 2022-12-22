using System.Diagnostics.Contracts;
using System.Linq;
using JetBrains.Annotations;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

class GhostInterestVisitor {
  readonly ICodeContext codeContext;
  readonly Resolver resolver;
  private readonly bool inConstructorInitializationPhase;
  public GhostInterestVisitor(ICodeContext codeContext, Resolver resolver, bool inConstructorInitializationPhase) {
    Contract.Requires(codeContext != null);
    Contract.Requires(resolver != null);
    this.codeContext = codeContext;
    this.resolver = resolver;
    this.inConstructorInitializationPhase = inConstructorInitializationPhase;
  }
  protected void Error(Statement stmt, string msg, params object[] msgArgs) {
    Contract.Requires(stmt != null);
    Contract.Requires(msg != null);
    Contract.Requires(msgArgs != null);
    resolver.reporter.Error(MessageSource.Resolver, stmt, msg, msgArgs);
  }
  protected void Error(Expression expr, string msg, params object[] msgArgs) {
    Contract.Requires(expr != null);
    Contract.Requires(msg != null);
    Contract.Requires(msgArgs != null);
    resolver.reporter.Error(MessageSource.Resolver, expr, msg, msgArgs);
  }
  protected void Error(IToken tok, string msg, params object[] msgArgs) {
    Contract.Requires(tok != null);
    Contract.Requires(msg != null);
    Contract.Requires(msgArgs != null);
    resolver.reporter.Error(MessageSource.Resolver, tok, msg, msgArgs);
  }
  /// <summary>
  /// There are three kinds of contexts for statements.
  ///   - compiled contexts, where the statement must be compilable
  ///     -- !mustBeErasable && proofContext == null
  ///   - ghost contexts that allow the allocation of new object
  ///     -- mustBeErasable && proofContext == null
  ///   - lemma/proof contexts, which are ghost and are not allowed to allocate new objects
  ///     -- mustBeErasable && proofContext != null
  /// 
  /// This method does three things, in order:
  /// 0. Sets .IsGhost to "true" if the statement is ghost.  This often depends on some guard of the statement
  ///    (like the guard of an "if" statement) or the LHS of the statement (if it is an assignment).
  ///    Note, if "mustBeErasable", then the statement is already in a ghost context.
  /// 1. Determines if the statement and all its subparts are legal under its computed .IsGhost setting.
  /// 2. ``Upgrades'' .IsGhost to "true" if, after investigation of the substatements of the statement, it
  ///    turns out that the statement can be erased during compilation.
  /// Notes:
  /// * Both step (0) and step (2) sets the .IsGhost field.  What step (0) does affects only the
  ///   rules of resolution, whereas step (2) makes a note for the later compilation phase.
  /// * It is important to do step (0) before step (1)--that is, it is important to set the statement's ghost
  ///   status before descending into its substatements--because break statements look at the ghost status of
  ///   its enclosing statements.
  /// * The method called by a StmtExpr must be ghost; however, this is checked elsewhere.  For
  ///   this reason, it is not necessary to visit all subexpressions, unless the subexpression
  ///   matter for the ghost checking/recording of "stmt".
  ///
  /// If "proofContext" is non-null, then this method also checks that "stmt" does not allocate
  /// memory or modify the heap, either directly or indirectly using a statement like "modify", a loop with
  /// an explicit "modifies" clause, or a call to a method that may allocate memory or modify the heap.
  /// The "proofContext" string is something that can be printed as part of an error message.
  /// </summary>
  public void Visit(Statement stmt, bool mustBeErasable, [CanBeNull] string proofContext) {
    Contract.Requires(stmt != null);
    Contract.Assume(!codeContext.IsGhost || mustBeErasable); // (this is really a precondition) CodeContext.IsGhost ==> mustBeErasable
    Contract.Assume(mustBeErasable || proofContext == null); // (this is really a precondition) !mustBeErasable ==> proofContext == null 

    if (stmt is AssertStmt || stmt is AssumeStmt) {
      stmt.IsGhost = true;
      var assertStmt = stmt as AssertStmt;
      if (assertStmt != null && assertStmt.Proof != null) {
        Visit(assertStmt.Proof, true, "an assert-by body");
      }

    } else if (stmt is ExpectStmt) {
      stmt.IsGhost = false;
      var s = (ExpectStmt)stmt;
      if (mustBeErasable) {
        Error(stmt, "expect statement is not allowed in this context (because this is a ghost method or because the statement is guarded by a specification-only expression)");
      } else {
        ExpressionTester.CheckIsCompilable(resolver, s.Expr, codeContext);
        // If not provided, the message is populated with a default value in resolution
        Contract.Assert(s.Message != null);
        ExpressionTester.CheckIsCompilable(resolver, s.Message, codeContext);
      }

    } else if (stmt is PrintStmt) {
      var s = (PrintStmt)stmt;
      if (mustBeErasable) {
        Error(stmt, "print statement is not allowed in this context (because this is a ghost method or because the statement is guarded by a specification-only expression)");
      } else {
        s.Args.Iter(ee => ExpressionTester.CheckIsCompilable(resolver, ee, codeContext));
      }

    } else if (stmt is RevealStmt) {
      var s = (RevealStmt)stmt;
      s.ResolvedStatements.Iter(ss => Visit(ss, true, "a reveal statement"));
      s.IsGhost = s.ResolvedStatements.All(ss => ss.IsGhost);

    } else if (stmt is BreakStmt) {
      var s = (BreakStmt)stmt;
      s.IsGhost = mustBeErasable;
      if (s.IsGhost && !s.TargetStmt.IsGhost) {
        var targetKind = s.TargetStmt is LoopStmt ? "loop" : "structure";
        Error(stmt, $"ghost-context {s.Kind} statement is not allowed to {s.Kind} out of non-ghost {targetKind}");
      }

    } else if (stmt is ProduceStmt) {
      var s = (ProduceStmt)stmt;
      var kind = stmt is YieldStmt ? "yield" : "return";
      if (mustBeErasable && !codeContext.IsGhost) {
        Error(stmt, "{0} statement is not allowed in this context (because it is guarded by a specification-only expression)", kind);
      }
      if (s.HiddenUpdate != null) {
        Visit(s.HiddenUpdate, mustBeErasable, proofContext);
      }

    } else if (stmt is AssignSuchThatStmt) {
      var s = (AssignSuchThatStmt)stmt;
      s.IsGhost = mustBeErasable || s.AssumeToken != null || s.Lhss.Any(AssignStmt.LhsIsToGhost);
      if (mustBeErasable && !codeContext.IsGhost) {
        foreach (var lhs in s.Lhss) {
          var gk = AssignStmt.LhsIsToGhost_Which(lhs);
          if (gk != AssignStmt.NonGhostKind.IsGhost) {
            Error(lhs, "cannot assign to {0} in a ghost context", AssignStmt.NonGhostKind_To_String(gk));
          }
        }
      } else if (!mustBeErasable && s.AssumeToken == null && ExpressionTester.UsesSpecFeatures(s.Expr)) {
        foreach (var lhs in s.Lhss) {
          var gk = AssignStmt.LhsIsToGhost_Which(lhs);
          if (gk != AssignStmt.NonGhostKind.IsGhost) {
            Error(lhs, "{0} cannot be assigned a value that depends on a ghost", AssignStmt.NonGhostKind_To_String(gk));
          }
        }
      }

    } else if (stmt is UpdateStmt) {
      var s = (UpdateStmt)stmt;
      s.ResolvedStatements.Iter(ss => Visit(ss, mustBeErasable, proofContext));
      s.IsGhost = s.ResolvedStatements.All(ss => ss.IsGhost);

    } else if (stmt is AssignOrReturnStmt) {
      var s = (AssignOrReturnStmt)stmt;
      s.ResolvedStatements.Iter(ss => Visit(ss, mustBeErasable, proofContext));
      s.IsGhost = s.ResolvedStatements.All(ss => ss.IsGhost);

    } else if (stmt is VarDeclStmt) {
      var s = (VarDeclStmt)stmt;
      if (mustBeErasable) {
        foreach (var local in s.Locals) {
          // a local variable in a specification-only context might as well be ghost
          local.MakeGhost();
        }
      }
      if (s.Update != null) {
        Visit(s.Update, mustBeErasable, proofContext);
      }
      s.IsGhost = (s.Update == null || s.Update.IsGhost) && s.Locals.All(v => v.IsGhost);

    } else if (stmt is VarDeclPattern) {
      var s = (VarDeclPattern)stmt;

      if (mustBeErasable) {
        foreach (var local in s.LocalVars) {
          local.MakeGhost();
        }
      }
      if (s.HasGhostModifier || mustBeErasable) {
        s.IsGhost = s.LocalVars.All(v => v.IsGhost);
      } else {
        var spec = ExpressionTester.UsesSpecFeatures(s.RHS);
        if (spec) {
          foreach (var local in s.LocalVars) {
            local.MakeGhost();
          }
        } else {
          ExpressionTester.CheckIsCompilable(resolver, s.RHS, codeContext);
        }
        s.IsGhost = spec;
      }

    } else if (stmt is AssignStmt) {
      var s = (AssignStmt)stmt;
      CheckAssignStmt(s, mustBeErasable, proofContext);

    } else if (stmt is CallStmt) {
      var s = (CallStmt)stmt;
      var callee = s.Method;
      Contract.Assert(callee != null);  // follows from the invariant of CallStmt
      s.IsGhost = callee.IsGhost;
      if (proofContext != null && !callee.IsLemmaLike) {
        Error(s, $"in {proofContext}, calls are allowed only to lemmas");
      } else if (mustBeErasable) {
        if (!s.IsGhost) {
          Error(s, "only ghost methods can be called from this context");
        }
      } else {
        int j;
        if (!callee.IsGhost) {
          // check in-parameters
          ExpressionTester.CheckIsCompilable(resolver, s.Receiver, codeContext);
          j = 0;
          foreach (var e in s.Args) {
            Contract.Assume(j < callee.Ins.Count);  // this should have already been checked by the resolver
            if (!callee.Ins[j].IsGhost) {
              ExpressionTester.CheckIsCompilable(resolver, e, codeContext);
            }
            j++;
          }
        }
        j = 0;
        foreach (var e in s.Lhs) {
          var resolvedLhs = e.Resolved;
          if (callee.IsGhost || callee.Outs[j].IsGhost) {
            // LHS must denote a ghost
            if (resolvedLhs is IdentifierExpr) {
              var ll = (IdentifierExpr)resolvedLhs;
              if (!ll.Var.IsGhost) {
                if (ll is AutoGhostIdentifierExpr && ll.Var is LocalVariable) {
                  // the variable was actually declared in this statement, so auto-declare it as ghost
                  ((LocalVariable)ll.Var).MakeGhost();
                } else {
                  Error(s, "actual out-parameter{0} is required to be a ghost variable", s.Lhs.Count == 1 ? "" : " " + j);
                }
              }
            } else if (resolvedLhs is MemberSelectExpr) {
              var ll = (MemberSelectExpr)resolvedLhs;
              if (!ll.Member.IsGhost) {
                Error(s, "actual out-parameter{0} is required to be a ghost field", s.Lhs.Count == 1 ? "" : " " + j);
              }
            } else {
              // this is an array update, and arrays are always non-ghost
              Error(s, "actual out-parameter{0} is required to be a ghost variable", s.Lhs.Count == 1 ? "" : " " + j);
            }
          }
          j++;
        }
      }

    } else if (stmt is BlockStmt) {
      var s = (BlockStmt)stmt;
      s.IsGhost = mustBeErasable;  // set .IsGhost before descending into substatements (since substatements may do a 'break' out of this block)
      if (s is DividedBlockStmt ds) {
        var giv = new GhostInterestVisitor(this.codeContext, this.resolver, true);
        ds.BodyInit.Iter(ss => giv.Visit(ss, mustBeErasable, proofContext));
        ds.BodyProper.Iter(ss => Visit(ss, mustBeErasable, proofContext));
      } else {
        s.Body.Iter(ss => Visit(ss, mustBeErasable, proofContext));
      }
      s.IsGhost = s.IsGhost || s.Body.All(ss => ss.IsGhost);  // mark the block statement as ghost if all its substatements are ghost

    } else if (stmt is IfStmt) {
      var s = (IfStmt)stmt;
      s.IsGhost = mustBeErasable || (s.Guard != null && ExpressionTester.UsesSpecFeatures(s.Guard));
      if (!mustBeErasable && s.IsGhost) {
        resolver.reporter.Info(MessageSource.Resolver, s.Tok, "ghost if");
      }
      Visit(s.Thn, s.IsGhost, proofContext);
      if (s.Els != null) {
        Visit(s.Els, s.IsGhost, proofContext);
      }
      // if both branches were all ghost, then we can mark the enclosing statement as ghost as well
      s.IsGhost = s.IsGhost || (s.Thn.IsGhost && (s.Els == null || s.Els.IsGhost));
      if (!s.IsGhost && s.Guard != null) {
        // If there were features in the guard that are treated differently in ghost and non-ghost
        // contexts, make sure they get treated for non-ghost use.
        ExpressionTester.CheckIsCompilable(resolver, s.Guard, codeContext);
      }

    } else if (stmt is AlternativeStmt) {
      var s = (AlternativeStmt)stmt;
      s.IsGhost = mustBeErasable || s.Alternatives.Exists(alt => ExpressionTester.UsesSpecFeatures(alt.Guard));
      if (!mustBeErasable && s.IsGhost) {
        resolver.reporter.Info(MessageSource.Resolver, s.Tok, "ghost if");
      }
      s.Alternatives.Iter(alt => alt.Body.Iter(ss => Visit(ss, s.IsGhost, proofContext)));
      s.IsGhost = s.IsGhost || s.Alternatives.All(alt => alt.Body.All(ss => ss.IsGhost));
      if (!s.IsGhost) {
        // If there were features in the guards that are treated differently in ghost and non-ghost
        // contexts, make sure they get treated for non-ghost use.
        foreach (var alt in s.Alternatives) {
          ExpressionTester.CheckIsCompilable(resolver, alt.Guard, codeContext);
        }
      }

    } else if (stmt is WhileStmt) {
      var s = (WhileStmt)stmt;
      if (proofContext != null && s.Mod.Expressions != null && s.Mod.Expressions.Count != 0) {
        Error(s.Mod.Expressions[0].tok, $"a loop in {proofContext} is not allowed to use 'modifies' clauses");
      }

      s.IsGhost = mustBeErasable || (s.Guard != null && ExpressionTester.UsesSpecFeatures(s.Guard));
      if (!mustBeErasable && s.IsGhost) {
        resolver.reporter.Info(MessageSource.Resolver, s.Tok, "ghost while");
      }
      if (s.IsGhost && s.Decreases.Expressions.Exists(e => e is WildcardExpr)) {
        Error(s, "'decreases *' is not allowed on ghost loops");
      }
      if (s.IsGhost && s.Mod.Expressions != null) {
        s.Mod.Expressions.Iter(resolver.DisallowNonGhostFieldSpecifiers);
      }
      if (s.Body != null) {
        Visit(s.Body, s.IsGhost, proofContext);
        if (s.Body.IsGhost && !s.Decreases.Expressions.Exists(e => e is WildcardExpr)) {
          s.IsGhost = true;
        }
      }
      if (!s.IsGhost && s.Guard != null) {
        // If there were features in the guard that are treated differently in ghost and non-ghost
        // contexts, make sure they get treated for non-ghost use.
        ExpressionTester.CheckIsCompilable(resolver, s.Guard, codeContext);
      }

    } else if (stmt is AlternativeLoopStmt) {
      var s = (AlternativeLoopStmt)stmt;
      if (proofContext != null && s.Mod.Expressions != null && s.Mod.Expressions.Count != 0) {
        Error(s.Mod.Expressions[0].tok, $"a loop in {proofContext} is not allowed to use 'modifies' clauses");
      }

      s.IsGhost = mustBeErasable || s.Alternatives.Exists(alt => ExpressionTester.UsesSpecFeatures(alt.Guard));
      if (!mustBeErasable && s.IsGhost) {
        resolver.reporter.Info(MessageSource.Resolver, s.Tok, "ghost while");
      }
      if (s.IsGhost && s.Decreases.Expressions.Exists(e => e is WildcardExpr)) {
        Error(s, "'decreases *' is not allowed on ghost loops");
      }
      if (s.IsGhost && s.Mod.Expressions != null) {
        s.Mod.Expressions.Iter(resolver.DisallowNonGhostFieldSpecifiers);
      }
      s.Alternatives.Iter(alt => alt.Body.Iter(ss => Visit(ss, s.IsGhost, proofContext)));
      s.IsGhost = s.IsGhost || (!s.Decreases.Expressions.Exists(e => e is WildcardExpr) && s.Alternatives.All(alt => alt.Body.All(ss => ss.IsGhost)));
      if (!s.IsGhost) {
        // If there were features in the guards that are treated differently in ghost and non-ghost
        // contexts, make sure they get treated for non-ghost use.
        foreach (var alt in s.Alternatives) {
          ExpressionTester.CheckIsCompilable(resolver, alt.Guard, codeContext);
        }
      }

    } else if (stmt is ForLoopStmt) {
      var s = (ForLoopStmt)stmt;
      if (proofContext != null && s.Mod.Expressions != null && s.Mod.Expressions.Count != 0) {
        Error(s.Mod.Expressions[0].tok, $"a loop in {proofContext} is not allowed to use 'modifies' clauses");
      }

      s.IsGhost = mustBeErasable || ExpressionTester.UsesSpecFeatures(s.Start) || (s.End != null && ExpressionTester.UsesSpecFeatures(s.End));
      if (!mustBeErasable && s.IsGhost) {
        resolver.reporter.Info(MessageSource.Resolver, s.Tok, "ghost for-loop");
      }
      if (s.IsGhost) {
        if (s.Decreases.Expressions.Exists(e => e is WildcardExpr)) {
          Error(s, "'decreases *' is not allowed on ghost loops");
        } else if (s.End == null && s.Decreases.Expressions.Count == 0) {
          Error(s, "a ghost loop must be terminating; make the end-expression specific or add a 'decreases' clause");
        }
      }
      if (s.IsGhost && s.Mod.Expressions != null) {
        s.Mod.Expressions.Iter(resolver.DisallowNonGhostFieldSpecifiers);
      }
      if (s.Body != null) {
        Visit(s.Body, s.IsGhost, proofContext);
        if (s.Body.IsGhost) {
          s.IsGhost = true;
        }
      }
      if (!s.IsGhost) {
        // If there were features in the bounds that are treated differently in ghost and non-ghost
        // contexts, make sure they get treated for non-ghost use.
        ExpressionTester.CheckIsCompilable(resolver, s.Start, codeContext);
        if (s.End != null) {
          ExpressionTester.CheckIsCompilable(resolver, s.End, codeContext);
        }
      }

    } else if (stmt is ForallStmt) {
      var s = (ForallStmt)stmt;
      s.IsGhost = mustBeErasable || s.Kind != ForallStmt.BodyKind.Assign || ExpressionTester.UsesSpecFeatures(s.Range);
      if (proofContext != null && s.Kind == ForallStmt.BodyKind.Assign) {
        Error(s, $"{proofContext} is not allowed to perform an aggregate heap update");
      } else if (s.Body != null) {
        Visit(s.Body, s.IsGhost, s.Kind == ForallStmt.BodyKind.Assign ? proofContext : "a forall statement");
      }
      s.IsGhost = s.IsGhost || s.Body == null || s.Body.IsGhost;

      if (!s.IsGhost) {
        // Since we've determined this is a non-ghost forall statement, we now check that the bound variables have compilable bounds.
        var uncompilableBoundVars = s.UncompilableBoundVars();
        if (uncompilableBoundVars.Count != 0) {
          foreach (var bv in uncompilableBoundVars) {
            Error(s, "forall statements in non-ghost contexts must be compilable, but Dafny's heuristics can't figure out how to produce or compile a bounded set of values for '{0}'", bv.Name);
          }
        }

        // If there were features in the range that are treated differently in ghost and non-ghost
        // contexts, make sure they get treated for non-ghost use.
        ExpressionTester.CheckIsCompilable(resolver, s.Range, codeContext);
      }

    } else if (stmt is ModifyStmt) {
      var s = (ModifyStmt)stmt;
      if (proofContext != null) {
        Error(stmt, $"a modify statement is not allowed in {proofContext}");
      }

      s.IsGhost = mustBeErasable;
      if (s.IsGhost) {
        s.Mod.Expressions.Iter(resolver.DisallowNonGhostFieldSpecifiers);
      }
      if (s.Body != null) {
        Visit(s.Body, mustBeErasable, proofContext);
      }

    } else if (stmt is CalcStmt) {
      var s = (CalcStmt)stmt;
      s.IsGhost = true;
      foreach (var h in s.Hints) {
        Visit(h, true, "a hint");
      }

    } else if (stmt is NestedMatchStmt nestedMatchStmt) {
      var hasGhostPattern = nestedMatchStmt.Cases.
        SelectMany(caze => caze.Pat.DescendantsAndSelf)
        .OfType<IdPattern>().Any(idPattern => idPattern.Ctor != null && idPattern.Ctor.IsGhost);
      nestedMatchStmt.IsGhost = mustBeErasable || ExpressionTester.UsesSpecFeatures(nestedMatchStmt.Source) || hasGhostPattern;
      
      if (!mustBeErasable && nestedMatchStmt.IsGhost) {
        resolver.reporter.Info(MessageSource.Resolver, nestedMatchStmt.Tok, "ghost match");
      }
      nestedMatchStmt.Cases.Iter(kase => kase.Body.Iter(ss => Visit(ss, nestedMatchStmt.IsGhost, proofContext)));
      nestedMatchStmt.IsGhost = nestedMatchStmt.IsGhost || nestedMatchStmt.Cases.All(kase => kase.Body.All(ss => ss.IsGhost));
      if (!nestedMatchStmt.IsGhost) {
        // If there were features in the source expression that are treated differently in ghost and non-ghost
        // contexts, make sure they get treated for non-ghost use.
        ExpressionTester.CheckIsCompilable(resolver, nestedMatchStmt.Source, codeContext);
      }
    } else if (stmt is MatchStmt) {
      var s = (MatchStmt)stmt;
      s.IsGhost = mustBeErasable || ExpressionTester.UsesSpecFeatures(s.Source) || ExpressionTester.FirstCaseThatDependsOnGhostCtor(s.Cases) != null;
      if (!mustBeErasable && s.IsGhost) {
        resolver.reporter.Info(MessageSource.Resolver, s.Tok, "ghost match");
      }
      s.Cases.Iter(kase => kase.Body.Iter(ss => Visit(ss, s.IsGhost, proofContext)));
      s.IsGhost = s.IsGhost || s.Cases.All(kase => kase.Body.All(ss => ss.IsGhost));
      if (!s.IsGhost) {
        // If there were features in the source expression that are treated differently in ghost and non-ghost
        // contexts, make sure they get treated for non-ghost use.
        ExpressionTester.CheckIsCompilable(resolver, s.Source, codeContext);
      }

    } else if (stmt is SkeletonStatement) {
      var s = (SkeletonStatement)stmt;
      s.IsGhost = mustBeErasable;
      if (s.S != null) {
        Visit(s.S, mustBeErasable, proofContext);
        s.IsGhost = s.IsGhost || s.S.IsGhost;
      }

    } else {
      Contract.Assert(false); throw new cce.UnreachableException();
    }
  }

  private void CheckAssignStmt(AssignStmt s, bool mustBeErasable, [CanBeNull] string proofContext) {
    Contract.Requires(s != null);
    Contract.Requires(mustBeErasable || proofContext == null);

    var lhs = s.Lhs.Resolved;

    // Make an auto-ghost variable a ghost if the RHS is a ghost
    if (lhs.Resolved is AutoGhostIdentifierExpr autoGhostIdExpr) {
      if (s.Rhs is ExprRhs eRhs && ExpressionTester.UsesSpecFeatures(eRhs.Expr)) {
        autoGhostIdExpr.Var.MakeGhost();
      } else if (s.Rhs is TypeRhs tRhs) {
        if (tRhs.InitCall != null && tRhs.InitCall.Method.IsGhost) {
          autoGhostIdExpr.Var.MakeGhost();
        } else if (tRhs.ArrayDimensions != null && tRhs.ArrayDimensions.Exists(ExpressionTester.UsesSpecFeatures)) {
          autoGhostIdExpr.Var.MakeGhost();
        } else if (tRhs.ElementInit != null && ExpressionTester.UsesSpecFeatures(tRhs.ElementInit)) {
          autoGhostIdExpr.Var.MakeGhost();
        } else if (tRhs.InitDisplay != null && tRhs.InitDisplay.Any(ExpressionTester.UsesSpecFeatures)) {
          autoGhostIdExpr.Var.MakeGhost();
        }
      }
    }

    if (proofContext != null && s.Rhs is TypeRhs) {
      Error(s.Rhs.Tok, $"{proofContext} is not allowed to use 'new'");
    }

    var gk = AssignStmt.LhsIsToGhost_Which(lhs);
    if (gk == AssignStmt.NonGhostKind.IsGhost) {
      s.IsGhost = true;
      if (proofContext != null && !(lhs is IdentifierExpr)) {
        Error(lhs.tok, $"{proofContext} is not allowed to make heap updates");
      }
      if (s.Rhs is TypeRhs tRhs && tRhs.InitCall != null) {
        Visit(tRhs.InitCall, true, proofContext);
      }
    } else if (gk == AssignStmt.NonGhostKind.Variable && codeContext.IsGhost) {
      // cool
    } else if (mustBeErasable) {
      if (inConstructorInitializationPhase && codeContext is Constructor && codeContext.IsGhost && lhs is MemberSelectExpr mse &&
          mse.Obj.Resolved is ThisExpr) {
        // in this first division (before "new;") of a ghost constructor, allow assignment to non-ghost field of the object being constructed
      } else {
        string reason;
        if (codeContext.IsGhost) {
          reason = string.Format("this is a ghost {0}", codeContext is MemberDecl member ? member.WhatKind : "context");
        } else {
          reason = "the statement is in a ghost context; e.g., it may be guarded by a specification-only expression";
        }
        Error(s, $"assignment to {AssignStmt.NonGhostKind_To_String(gk)} is not allowed in this context, because {reason}");
      }
    } else {
      if (gk == AssignStmt.NonGhostKind.Field) {
        var mse = (MemberSelectExpr)lhs;
        ExpressionTester.CheckIsCompilable(resolver, mse.Obj, codeContext);
      } else if (gk == AssignStmt.NonGhostKind.ArrayElement) {
        ExpressionTester.CheckIsCompilable(resolver, lhs, codeContext);
      }

      if (s.Rhs is ExprRhs) {
        var rhs = (ExprRhs)s.Rhs;
        if (!AssignStmt.LhsIsToGhost(lhs)) {
          ExpressionTester.CheckIsCompilable(resolver, rhs.Expr, codeContext);
        }
      } else if (s.Rhs is HavocRhs) {
        // cool
      } else {
        var rhs = (TypeRhs)s.Rhs;
        if (rhs.ArrayDimensions != null) {
          rhs.ArrayDimensions.ForEach(ee => ExpressionTester.CheckIsCompilable(resolver, ee, codeContext));
          if (rhs.ElementInit != null) {
            ExpressionTester.CheckIsCompilable(resolver, rhs.ElementInit, codeContext);
          }
          if (rhs.InitDisplay != null) {
            rhs.InitDisplay.ForEach(ee => ExpressionTester.CheckIsCompilable(resolver, ee, codeContext));
          }
        }
        if (rhs.InitCall != null) {
          var callee = rhs.InitCall.Method;
          if (callee.IsGhost) {
            Error(rhs.InitCall, "the result of a ghost constructor can only be assigned to a ghost variable");
          }
          for (var i = 0; i < rhs.InitCall.Args.Count; i++) {
            if (!callee.Ins[i].IsGhost) {
              ExpressionTester.CheckIsCompilable(resolver, rhs.InitCall.Args[i], codeContext);
            }
          }
        }
      }
    }
  }
}
