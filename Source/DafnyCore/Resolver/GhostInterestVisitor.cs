using System.Diagnostics.Contracts;
using System.Linq;
using JetBrains.Annotations;
using Microsoft.Boogie;
using static Microsoft.Dafny.ResolutionErrors;

namespace Microsoft.Dafny;

class GhostInterestVisitor {
  readonly ICodeContext codeContext;
  readonly ModuleResolver resolver;
  private readonly ErrorReporter reporter;
  private readonly bool inConstructorInitializationPhase;
  private readonly bool allowAssumptionVariables;
  public GhostInterestVisitor(ICodeContext codeContext, ModuleResolver resolver, ErrorReporter reporter, bool inConstructorInitializationPhase, bool allowAssumptionVariables) {
    Contract.Requires(codeContext != null);
    Contract.Requires(resolver != null);
    this.codeContext = codeContext;
    this.resolver = resolver;
    this.reporter = reporter;
    this.inConstructorInitializationPhase = inConstructorInitializationPhase;
    this.allowAssumptionVariables = allowAssumptionVariables;
  }
  protected void Error(ErrorId errorId, Statement stmt, string msg, params object[] msgArgs) {
    Contract.Requires(stmt != null);
    Contract.Requires(msg != null);
    Contract.Requires(msgArgs != null);
    reporter.Error(MessageSource.Resolver, errorId, stmt, msg, msgArgs);
  }
  protected void Error(ErrorId errorId, Expression expr, string msg, params object[] msgArgs) {
    Contract.Requires(expr != null);
    Contract.Requires(msg != null);
    Contract.Requires(msgArgs != null);
    reporter.Error(MessageSource.Resolver, errorId, expr, msg, msgArgs);
  }
  protected void Error(ErrorId errorId, IOrigin tok, string msg, params object[] msgArgs) {
    Contract.Requires(tok != null);
    Contract.Requires(msg != null);
    Contract.Requires(msgArgs != null);
    reporter.Error(MessageSource.Resolver, errorId, tok, msg, msgArgs);
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

    switch (stmt) {
      case AssertStmt or AssumeStmt:
        stmt.IsGhost = true;
        break;
      case ExpectStmt expectStmt: {
          expectStmt.IsGhost = false;
          if (mustBeErasable) {
            Error(ErrorId.r_expect_statement_is_not_ghost, expectStmt, "expect statement is not allowed in this context (because this is a ghost method or because the statement is guarded by a specification-only expression)");
          } else {
            ExpressionTester.CheckIsCompilable(resolver, reporter, expectStmt.Expr, codeContext);
            // If not provided, the message is populated with a default value in resolution
            Contract.Assert(expectStmt.Message != null);
            ExpressionTester.CheckIsCompilable(resolver, reporter, expectStmt.Message, codeContext);
          }

          break;
        }
      case PrintStmt printStmt: {
          var s = printStmt;
          if (mustBeErasable) {
            Error(ErrorId.r_print_statement_is_not_ghost, printStmt, "print statement is not allowed in this context (because this is a ghost method or because the statement is guarded by a specification-only expression)");
          } else {
            s.Args.ForEach(ee => ExpressionTester.CheckIsCompilable(resolver, reporter, ee, codeContext));
          }

          break;
        }
      case HideRevealStmt hideRevealStmt:
        hideRevealStmt.ResolvedStatements.ForEach(ss => Visit(ss, true, $"a {hideRevealStmt.Kind} statement"));
        hideRevealStmt.IsGhost = hideRevealStmt.ResolvedStatements.All(ss => ss.IsGhost);
        break;
      case BreakOrContinueStmt breakStmt: {
          var s = breakStmt;
          s.IsGhost = mustBeErasable;
          if (s.IsGhost && !s.TargetStmt.IsGhost) {
            var targetKind = s.TargetStmt is LoopStmt ? "loop" : "structure";
            Error(ErrorId.r_ghost_break, breakStmt, $"ghost-context {s.Kind} statement is not allowed to {s.Kind} out of non-ghost {targetKind}");
          }

          break;
        }
      case ProduceStmt produceStmt: {
          var s = produceStmt;
          var kind = produceStmt is YieldStmt ? "yield" : "return";
          if (mustBeErasable && !codeContext.IsGhost) {
            Error(ErrorId.r_produce_statement_not_allowed_in_ghost, produceStmt, "{0} statement is not allowed in this context (because it is guarded by a specification-only expression)", kind);
          }
          if (s.HiddenUpdate != null) {
            Visit(s.HiddenUpdate, mustBeErasable, proofContext);
          }

          break;
        }
      case AssignSuchThatStmt thatStmt: {
          var s = thatStmt;
          s.IsGhost = mustBeErasable || s.AssumeToken != null || s.Lhss.Any(SingleAssignStmt.LhsIsToGhost);
          if (mustBeErasable && !codeContext.IsGhost) {
            foreach (var lhs in s.Lhss) {
              var gk = SingleAssignStmt.LhsIsToGhost_Which(lhs);
              if (gk != SingleAssignStmt.NonGhostKind.IsGhost) {
                Error(ErrorId.r_no_assign_to_var_in_ghost, lhs, "cannot assign to {0} in a ghost context", SingleAssignStmt.NonGhostKind_To_String(gk));
              }
            }
          } else if (!mustBeErasable && s.AssumeToken == null && ExpressionTester.UsesSpecFeatures(s.Expr)) {
            foreach (var lhs in s.Lhss) {
              var gk = SingleAssignStmt.LhsIsToGhost_Which(lhs);
              if (gk != SingleAssignStmt.NonGhostKind.IsGhost) {
                Error(ErrorId.r_no_assign_ghost_to_var, lhs, "{0} cannot be assigned a value that depends on a ghost", SingleAssignStmt.NonGhostKind_To_String(gk));
              }
            }
          }

          break;
        }
      case AssignStatement statement: {
          var s = statement;
          s.ResolvedStatements.ForEach(ss => Visit(ss, mustBeErasable, proofContext));
          s.IsGhost = s.ResolvedStatements.All(ss => ss.IsGhost);
          break;
        }
      case AssignOrReturnStmt returnStmt: {
          var s = returnStmt;
          s.ResolvedStatements.ForEach(ss => Visit(ss, mustBeErasable, proofContext));
          s.IsGhost = s.ResolvedStatements.All(ss => ss.IsGhost);
          break;
        }
      case VarDeclStmt declStmt: {
          var s = declStmt;
          if (mustBeErasable) {
            foreach (var local in s.Locals) {
              // a local variable in a specification-only context might as well be ghost
              local.MakeGhost();
            }
          }
          if (s.Assign != null) {
            Visit(s.Assign, mustBeErasable, proofContext);
          }
          s.IsGhost = (s.Assign == null || s.Assign.IsGhost) && s.Locals.All(v => v.IsGhost);

          // Check on "assumption" variables
          foreach (var local in s.Locals) {
            if (Attributes.Contains(local.Attributes, "assumption")) {
              if (allowAssumptionVariables) {
                if (!local.Type.IsBoolType) {
                  Error(ErrorId.r_assumption_var_must_be_bool, local.Origin, "assumption variable must be of type 'bool'");
                }
                if (!local.IsGhost) {
                  Error(ErrorId.r_assumption_var_must_be_ghost, local.Origin, "assumption variable must be ghost");
                }
              } else {
                Error(ErrorId.r_assumption_var_must_be_in_method, local.Origin, "assumption variable can only be declared in a method");
              }
            }
          }

          break;
        }
      case VarDeclPattern pattern: {
          var s = pattern;

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
              ExpressionTester.CheckIsCompilable(resolver, reporter, s.RHS, codeContext);
            }
            s.IsGhost = spec;
          }

          break;
        }
      case SingleAssignStmt assignStmt: {
          var s = assignStmt;
          CheckAssignStmt(s, mustBeErasable, proofContext);
          break;
        }
      case CallStmt callStmt: {
          var s = callStmt;
          var callee = s.Method;
          Contract.Assert(callee != null);  // follows from the invariant of CallStmt
          s.IsGhost = callee.IsGhost;
          if (proofContext != null && !callee.IsLemmaLike) {
            Error(ErrorId.r_no_calls_in_proof, s, $"in {proofContext}, calls are allowed only to lemmas");
          } else if (mustBeErasable) {
            if (!s.IsGhost) {
              Error(ErrorId.r_only_ghost_calls, s, "only ghost methods can be called from this context");
            }
          } else {
            int j;
            if (!callee.IsGhost) {
              // check in-parameters
              ExpressionTester.CheckIsCompilable(resolver, reporter, s.Receiver, codeContext);
              j = 0;
              foreach (var e in s.Args) {
                Contract.Assume(j < callee.Ins.Count);  // this should have already been checked by the resolver
                if (!callee.Ins[j].IsGhost) {
                  ExpressionTester.CheckIsCompilable(resolver, reporter, e, codeContext);
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
                      Error(ErrorId.r_out_parameter_must_be_ghost, s, "actual out-parameter{0} is required to be a ghost variable", s.Lhs.Count == 1 ? "" : " " + j);
                    }
                  }
                } else if (resolvedLhs is MemberSelectExpr) {
                  var ll = (MemberSelectExpr)resolvedLhs;
                  if (!ll.Member.IsGhost) {
                    Error(ErrorId.r_out_parameter_must_be_ghost_field, s, "actual out-parameter{0} is required to be a ghost field", s.Lhs.Count == 1 ? "" : " " + j);
                  }
                } else {
                  // this is an array update, and arrays are always non-ghost
                  Error(ErrorId.r_out_parameter_must_be_ghost, s, "actual out-parameter{0} is required to be a ghost variable", s.Lhs.Count == 1 ? "" : " " + j);
                }
              }
              j++;
            }
          }

          break;
        }
      case BlockLikeStmt blockStmt: {
          var s = blockStmt;
          s.IsGhost = mustBeErasable;  // set .IsGhost before descending into substatements (since substatements may do a 'break' out of this block)
          if (s is DividedBlockStmt ds) {
            var giv = new GhostInterestVisitor(this.codeContext, this.resolver, this.reporter, true, allowAssumptionVariables);
            ds.BodyInit.ForEach(ss => giv.Visit(ss, mustBeErasable, proofContext));
            ds.BodyProper.ForEach(ss => Visit(ss, mustBeErasable, proofContext));
          } else {
            s.Body.ForEach(ss => Visit(ss, mustBeErasable, proofContext));
          }
          s.IsGhost = s.IsGhost || s.Body.All(ss => ss.IsGhost);  // mark the block statement as ghost if all its substatements are ghost
          break;
        }
      case IfStmt ifStmt: {
          var s = ifStmt;
          s.IsGhost = mustBeErasable || (s.Guard != null && ExpressionTester.UsesSpecFeatures(s.Guard));
          if (!mustBeErasable && s.IsGhost) {
            reporter.Info(MessageSource.Resolver, s.Origin, "ghost if");
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
            ExpressionTester.CheckIsCompilable(resolver, reporter, s.Guard, codeContext);
          }

          break;
        }
      case AlternativeStmt alternativeStmt: {
          var s = alternativeStmt;
          s.IsGhost = mustBeErasable || s.Alternatives.Exists(alt => ExpressionTester.UsesSpecFeatures(alt.Guard));
          if (!mustBeErasable && s.IsGhost) {
            reporter.Info(MessageSource.Resolver, s.Origin, "ghost if");
          }
          s.Alternatives.ForEach(alt => alt.Body.ForEach(ss => Visit(ss, s.IsGhost, proofContext)));
          s.IsGhost = s.IsGhost || s.Alternatives.All(alt => alt.Body.All(ss => ss.IsGhost));
          if (!s.IsGhost) {
            // If there were features in the guards that are treated differently in ghost and non-ghost
            // contexts, make sure they get treated for non-ghost use.
            foreach (var alt in s.Alternatives) {
              ExpressionTester.CheckIsCompilable(resolver, reporter, alt.Guard, codeContext);
            }
          }

          break;
        }
      case WhileStmt whileStmt: {
          var s = whileStmt;
          if (proofContext != null && s.Mod.Expressions != null && s.Mod.Expressions.Count != 0) {
            Error(ErrorId.r_loop_may_not_use_modifies, s.Mod.Expressions[0].Origin, $"a loop in {proofContext} is not allowed to use 'modifies' clauses");
          }

          s.IsGhost = mustBeErasable || (s.Guard != null && ExpressionTester.UsesSpecFeatures(s.Guard));
          if (!mustBeErasable && s.IsGhost) {
            reporter.Info(MessageSource.Resolver, s.Origin, "ghost while");
          }
          if (s.IsGhost && s.Decreases.Expressions.Exists(e => e is WildcardExpr)) {
            Error(ErrorId.r_decreases_forbidden_on_ghost_loops, s, "'decreases *' is not allowed on ghost loops");
          }
          if (s.IsGhost && s.Mod.Expressions != null) {
            s.Mod.Expressions.ForEach(resolver.DisallowNonGhostFieldSpecifiers);
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
            ExpressionTester.CheckIsCompilable(resolver, reporter, s.Guard, codeContext);
          }

          break;
        }
      case AlternativeLoopStmt loopStmt: {
          var s = loopStmt;
          if (proofContext != null && s.Mod.Expressions != null && s.Mod.Expressions.Count != 0) {
            Error(ErrorId.r_loop_in_proof_may_not_use_modifies, s.Mod.Expressions[0].Origin, $"a loop in {proofContext} is not allowed to use 'modifies' clauses");
          }

          s.IsGhost = mustBeErasable || s.Alternatives.Exists(alt => ExpressionTester.UsesSpecFeatures(alt.Guard));
          if (!mustBeErasable && s.IsGhost) {
            reporter.Info(MessageSource.Resolver, s.Origin, "ghost while");
          }
          if (s.IsGhost && s.Decreases.Expressions.Exists(e => e is WildcardExpr)) {
            Error(ErrorId.r_decreases_forbidden_on_ghost_loops, s, "'decreases *' is not allowed on ghost loops");
          }
          if (s.IsGhost && s.Mod.Expressions != null) {
            s.Mod.Expressions.ForEach(resolver.DisallowNonGhostFieldSpecifiers);
          }
          s.Alternatives.ForEach(alt => alt.Body.ForEach(ss => Visit(ss, s.IsGhost, proofContext)));
          s.IsGhost = s.IsGhost || (!s.Decreases.Expressions.Exists(e => e is WildcardExpr) && s.Alternatives.All(alt => alt.Body.All(ss => ss.IsGhost)));
          if (!s.IsGhost) {
            // If there were features in the guards that are treated differently in ghost and non-ghost
            // contexts, make sure they get treated for non-ghost use.
            foreach (var alt in s.Alternatives) {
              ExpressionTester.CheckIsCompilable(resolver, reporter, alt.Guard, codeContext);
            }
          }

          break;
        }
      case ForLoopStmt loopStmt: {
          var s = loopStmt;
          if (proofContext != null && s.Mod.Expressions != null && s.Mod.Expressions.Count != 0) {
            Error(ErrorId.r_loop_in_proof_may_not_use_modifies, s.Mod.Expressions[0].Origin, $"a loop in {proofContext} is not allowed to use 'modifies' clauses");
          }

          s.IsGhost = mustBeErasable || ExpressionTester.UsesSpecFeatures(s.Start) || (s.End != null && ExpressionTester.UsesSpecFeatures(s.End));
          if (!mustBeErasable && s.IsGhost) {
            reporter.Info(MessageSource.Resolver, s.Origin, "ghost for-loop");
          }
          if (s.IsGhost) {
            if (s.Decreases.Expressions.Exists(e => e is WildcardExpr)) {
              Error(ErrorId.r_decreases_forbidden_on_ghost_loops, s, "'decreases *' is not allowed on ghost loops");
            } else if (s.End == null && s.Decreases.Expressions.Count == 0) {
              Error(ErrorId.r_ghost_loop_must_terminate, s, "a ghost loop must be terminating; make the end-expression specific or add a 'decreases' clause");
            }
          }
          if (s.IsGhost && s.Mod.Expressions != null) {
            s.Mod.Expressions.ForEach(resolver.DisallowNonGhostFieldSpecifiers);
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
            ExpressionTester.CheckIsCompilable(resolver, reporter, s.Start, codeContext);
            if (s.End != null) {
              ExpressionTester.CheckIsCompilable(resolver, reporter, s.End, codeContext);
            }
          }

          break;
        }
      case ForallStmt forallStmt: {
          var s = forallStmt;
          s.IsGhost = mustBeErasable || s.Kind != ForallStmt.BodyKind.Assign || ExpressionTester.UsesSpecFeatures(s.Range);
          if (proofContext != null && s.Kind == ForallStmt.BodyKind.Assign) {
            Error(ErrorId.r_no_aggregate_heap_update_in_proof, s, $"{proofContext} is not allowed to perform an aggregate heap update");
          } else if (s.Body != null) {
            Visit(s.Body, s.IsGhost, s.Kind == ForallStmt.BodyKind.Assign ? proofContext : "a forall statement");
          }
          s.IsGhost = s.IsGhost || s.Body == null || s.Body.IsGhost;

          if (!s.IsGhost) {
            // Since we've determined this is a non-ghost forall statement, we now check that the bound variables have compilable bounds.
            var uncompilableBoundVars = s.UncompilableBoundVars();
            if (uncompilableBoundVars.Count != 0) {
              foreach (var bv in uncompilableBoundVars) {
                Error(ErrorId.r_unknown_bounds_for_forall, s, "forall statements in non-ghost contexts must be compilable, but Dafny's heuristics can't figure out how to produce or compile a bounded set of values for '{0}'", bv.Name);
              }
            }

            // If there were features in the range that are treated differently in ghost and non-ghost
            // contexts, make sure they get treated for non-ghost use.
            ExpressionTester.CheckIsCompilable(resolver, reporter, s.Range, codeContext);
          }

          break;
        }
      case ModifyStmt modifyStmt: {
          var s = modifyStmt;
          if (proofContext != null) {
            Error(ErrorId.r_modify_forbidden_in_proof, modifyStmt, $"a modify statement is not allowed in {proofContext}");
          }

          s.IsGhost = mustBeErasable;
          if (s.IsGhost) {
            s.Mod.Expressions.ForEach(resolver.DisallowNonGhostFieldSpecifiers);
          }
          if (s.Body != null) {
            Visit(s.Body, mustBeErasable, proofContext);
          }

          break;
        }
      case CalcStmt calcStmt: {
          var s = calcStmt;
          s.IsGhost = true;
          foreach (var h in s.Hints) {
            Visit(h, true, "a hint");
          }

          break;
        }
      case NestedMatchStmt nestedMatchStmt: {
          var hasGhostPattern = nestedMatchStmt.Cases.
            SelectMany(caze => caze.Pat.DescendantsAndSelf)
            .OfType<IdPattern>().Any(idPattern => idPattern.Ctor != null && idPattern.Ctor.IsGhost);
          nestedMatchStmt.IsGhost = mustBeErasable || ExpressionTester.UsesSpecFeatures(nestedMatchStmt.Source) || hasGhostPattern;

          foreach (var kase in nestedMatchStmt.Cases) {
            ExpressionTester.MakeGhostAsNeeded(kase.Pat, nestedMatchStmt.IsGhost);
          }

          if (!mustBeErasable && nestedMatchStmt.IsGhost) {
            reporter.Info(MessageSource.Resolver, nestedMatchStmt.Origin, "ghost match");
          }
          nestedMatchStmt.Cases.ForEach(kase => kase.Body.ForEach(ss => Visit(ss, nestedMatchStmt.IsGhost, proofContext)));
          nestedMatchStmt.IsGhost = nestedMatchStmt.IsGhost || nestedMatchStmt.Cases.All(kase => kase.Body.All(ss => ss.IsGhost));
          if (!nestedMatchStmt.IsGhost) {
            // If there were features in the source expression that are treated differently in ghost and non-ghost
            // contexts, make sure they get treated for non-ghost use.
            ExpressionTester.CheckIsCompilable(resolver, reporter, nestedMatchStmt.Source, codeContext);
          }

          break;
        }
      case MatchStmt matchStmt: {
          var s = matchStmt;
          s.IsGhost = mustBeErasable || ExpressionTester.UsesSpecFeatures(s.Source) || ExpressionTester.FirstCaseThatDependsOnGhostCtor(s.Cases) != null;
          if (!mustBeErasable && s.IsGhost) {
            reporter.Info(MessageSource.Resolver, s.Origin, "ghost match");
          }
          s.Cases.ForEach(kase => kase.Body.ForEach(ss => Visit(ss, s.IsGhost, proofContext)));
          s.IsGhost = s.IsGhost || s.Cases.All(kase => kase.Body.All(ss => ss.IsGhost));
          if (!s.IsGhost) {
            // If there were features in the source expression that are treated differently in ghost and non-ghost
            // contexts, make sure they get treated for non-ghost use.
            ExpressionTester.CheckIsCompilable(resolver, reporter, s.Source, codeContext);
          }

          break;
        }
      case SkeletonStatement statement: {
          var s = statement;
          s.IsGhost = mustBeErasable;
          if (s.S != null) {
            Visit(s.S, mustBeErasable, proofContext);
            s.IsGhost = s.IsGhost || s.S.IsGhost;
          }

          break;
        }
      case BlockByProofStmt blockByProofStmt:
        blockByProofStmt.IsGhost = mustBeErasable;  // set .IsGhost before descending into substatements (since substatements may do a 'break' out of this block)
        Visit(blockByProofStmt.Body, mustBeErasable, proofContext);
        blockByProofStmt.IsGhost = blockByProofStmt.IsGhost || blockByProofStmt.Body.IsGhost;

        Visit(blockByProofStmt.Proof, true, "a by block");
        break;
      default:
        Contract.Assert(false); throw new cce.UnreachableException();
    }
  }

  private void CheckAssignStmt(SingleAssignStmt s, bool mustBeErasable, [CanBeNull] string proofContext) {
    Contract.Requires(s != null);
    Contract.Requires(mustBeErasable || proofContext == null);

    var lhs = s.Lhs.Resolved;

    // Make an auto-ghost variable a ghost if the RHS is a ghost
    if (lhs.Resolved is AutoGhostIdentifierExpr autoGhostIdExpr) {
      if (s.Rhs is ExprRhs eRhs && ExpressionTester.UsesSpecFeatures(eRhs.Expr)) {
        autoGhostIdExpr.Var.MakeGhost();
      } else if (s.Rhs is AllocateClass allocateClass) {
        if (allocateClass.InitCall != null && allocateClass.InitCall.Method.IsGhost) {
          autoGhostIdExpr.Var.MakeGhost();
        }
      } else if (s.Rhs is AllocateArray allocateArray) {
        if (allocateArray.ArrayDimensions.Exists(ExpressionTester.UsesSpecFeatures)) {
          autoGhostIdExpr.Var.MakeGhost();
        } else if (allocateArray.ElementInit != null && ExpressionTester.UsesSpecFeatures(allocateArray.ElementInit)) {
          autoGhostIdExpr.Var.MakeGhost();
        } else if (allocateArray.InitDisplay != null && allocateArray.InitDisplay.Any(ExpressionTester.UsesSpecFeatures)) {
          autoGhostIdExpr.Var.MakeGhost();
        }
      }
    }

    if (proofContext != null && s.Rhs is TypeRhs) {
      Error(ErrorId.r_new_forbidden_in_proof, s.Rhs.Origin, $"{proofContext} is not allowed to use 'new'");
    }

    var gk = SingleAssignStmt.LhsIsToGhost_Which(lhs);
    if (gk == SingleAssignStmt.NonGhostKind.IsGhost) {
      s.IsGhost = true;
      if (proofContext != null && !(lhs is IdentifierExpr)) {
        Error(ErrorId.r_no_heap_update_in_proof, lhs.Origin, $"{proofContext} is not allowed to make heap updates");
      }
      if (s.Rhs is AllocateClass { InitCall: not null } tRhs) {
        Visit(tRhs.InitCall, true, proofContext);
      }
    } else if (gk == SingleAssignStmt.NonGhostKind.Variable && codeContext.IsGhost) {
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
        Error(ErrorId.r_assignment_forbidden_in_context, s, $"assignment to {SingleAssignStmt.NonGhostKind_To_String(gk)} is not allowed in this context, because {reason}");
      }
    } else {
      if (gk == SingleAssignStmt.NonGhostKind.Field) {
        var mse = (MemberSelectExpr)lhs;
        ExpressionTester.CheckIsCompilable(resolver, reporter, mse.Obj, codeContext);
      } else if (gk == SingleAssignStmt.NonGhostKind.ArrayElement) {
        ExpressionTester.CheckIsCompilable(resolver, reporter, lhs, codeContext);
      }

      if (s.Rhs is ExprRhs) {
        var rhs = (ExprRhs)s.Rhs;
        if (!SingleAssignStmt.LhsIsToGhost(lhs)) {
          ExpressionTester.CheckIsCompilable(resolver, reporter, rhs.Expr, codeContext);
        }
      } else if (s.Rhs is HavocRhs) {
        // cool
      } else if (s.Rhs is AllocateArray allocateArray) {
        var rhs = (TypeRhs)s.Rhs;
        allocateArray.ArrayDimensions.ForEach(ee =>
          ExpressionTester.CheckIsCompilable(resolver, reporter, ee, codeContext));
        if (allocateArray.ElementInit != null) {
          ExpressionTester.CheckIsCompilable(resolver, reporter, allocateArray.ElementInit, codeContext);
        }

        if (allocateArray.InitDisplay != null) {
          allocateArray.InitDisplay.ForEach(ee =>
            ExpressionTester.CheckIsCompilable(resolver, reporter, ee, codeContext));
        }
      } else if (s.Rhs is AllocateClass allocateClass) {
        if (allocateClass.InitCall != null) {
          var callee = allocateClass.InitCall.Method;
          if (callee.IsGhost) {
            Error(ErrorId.r_assignment_to_ghost_constructor_only_in_ghost, allocateClass.InitCall, "the result of a ghost constructor can only be assigned to a ghost variable");
          }
          for (var i = 0; i < allocateClass.InitCall.Args.Count; i++) {
            if (!callee.Ins[i].IsGhost) {
              ExpressionTester.CheckIsCompilable(resolver, reporter, allocateClass.InitCall.Args[i], codeContext);
            }
          }
        }
      }
    }
  }
}
