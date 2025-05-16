//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics.Contracts;
using JetBrains.Annotations;
using RAST;

namespace Microsoft.Dafny {
  public partial class PreTypeResolver : INewOrOldResolver {
    public Scope<Label> DominatingStatementLabels { get; }

    public Scope<LabeledStatement> EnclosingStatementLabels { get; set; }

    public List<LabeledStatement> LoopStack {
      get => loopStack;
      set => loopStack = value;
    }

    private List<LabeledStatement> loopStack = [];  // the enclosing loops (from which it is possible to break out)

    public void ResolveBlockStatement(BlockLikeStmt blockStmt, ResolutionContext resolutionContext) {
      Contract.Requires(blockStmt != null);
      Contract.Requires(resolutionContext != null);

      if (blockStmt is DividedBlockStmt div) {
        Contract.Assert(currentMethod is Constructor);  // divided bodies occur only in class constructors
        foreach (Statement ss in div.BodyInit) {
          ResolveStatementWithLabels(ss, resolutionContext with { InFirstPhaseConstructor = true });
        }
        foreach (Statement ss in div.BodyProper) {
          ResolveStatementWithLabels(ss, resolutionContext);
        }
      } else {
        foreach (Statement ss in blockStmt.Body) {
          ResolveStatementWithLabels(ss, resolutionContext);
        }
      }
    }

    public void ResolveStatementWithLabels(Statement stmt, ResolutionContext resolutionContext) {
      Contract.Requires(stmt != null);
      Contract.Requires(resolutionContext != null);

      EnclosingStatementLabels.PushMarker();
      // push labels
      if (stmt is LabeledStatement labelledStatement) {
        foreach (var lnode in labelledStatement.Labels) {
          Contract.Assert(lnode.Name != null);  // Label's with .Name==null are added only during resolution of the break statements with 'stmt' as their target, which hasn't happened yet
          var prev = EnclosingStatementLabels.Find(lnode.Name);
          if (prev == stmt) {
            ReportError(lnode.Tok, "duplicate label");
          } else if (prev != null) {
            ReportError(lnode.Tok, "label shadows an enclosing label");
          } else {
            var r = EnclosingStatementLabels.Push(lnode.Name, labelledStatement);
            Contract.Assert(r == Scope<LabeledStatement>.PushResult.Success);  // since we just checked for duplicates, we expect the Push to succeed
            if (DominatingStatementLabels.Find(lnode.Name) != null) {
              ReportError(lnode.Tok, "label shadows a dominating label");
            } else {
              var rr = DominatingStatementLabels.Push(lnode.Name, lnode);
              Contract.Assert(rr == Scope<Label>.PushResult.Success);  // since we just checked for duplicates, we expect the Push to succeed
            }
          }
        }
      }
      ResolveStatement(stmt, resolutionContext);
      EnclosingStatementLabels.PopMarker();
    }

    Label/*?*/ ResolveDominatingLabelInExpr(IOrigin tok, string/*?*/ labelName, string expressionDescription, ResolutionContext resolutionContext) {
      Contract.Requires(tok != null);
      Contract.Requires(expressionDescription != null);
      Contract.Requires(resolutionContext != null);

      Label label = null;
      if (!resolutionContext.IsTwoState) {
        ReportError(tok, $"{expressionDescription} expressions are not allowed in this context");
      } else if (labelName != null) {
        label = DominatingStatementLabels.Find(labelName);
        if (label == null) {
          ReportError(tok, $"no label '{labelName}' in scope at this time");
        }
      }
      return label;
    }

    public void ResolveStatement(Statement stmt, ResolutionContext resolutionContext) {
      Contract.Requires(stmt != null);
      Contract.Requires(resolutionContext != null);

      if (stmt is ICanResolveNewAndOld canResolve) {
        canResolve.GenResolve(this, resolutionContext);
        return;
      }

      if (!(stmt is ForallStmt or ForLoopStmt)) {  // "forall" and "for" statements do their own attribute resolution below
        ResolveAttributes(stmt, resolutionContext, false);
      }
      if (stmt is PrintStmt) {
        var s = (PrintStmt)stmt;
        foreach (var e in s.Args) {
          ResolveExpression(e, resolutionContext);
        }

      } else if (stmt is BreakOrContinueStmt) {
        var s = (BreakOrContinueStmt)stmt;
        if (s.TargetLabel != null) {
          var target = EnclosingStatementLabels.Find(s.TargetLabel.Value);
          if (target == null) {
            ReportError(s.TargetLabel.Origin, $"{s.Kind} label is undefined or not in scope: {s.TargetLabel.Value}");
          } else if (s.IsContinue && !(target is LoopStmt)) {
            ReportError(s.TargetLabel.Origin, $"continue label must designate a loop: {s.TargetLabel.Value}");
          } else {
            s.TargetStmt = target;
          }
        } else {
          Contract.Assert(1 <= s.BreakAndContinueCount); // follows from BreakStmt class invariant and the guard for this "else" branch
          var jumpStmt = s.BreakAndContinueCount == 1 ?
            $"a non-labeled '{s.Kind}' statement" :
            $"a '{Util.Repeat(s.BreakAndContinueCount - 1, "break ")}{s.Kind}' statement";
          if (loopStack.Count == 0) {
            ReportError(s, $"{jumpStmt} is allowed only in loops");
          } else if (loopStack.Count < s.BreakAndContinueCount) {
            ReportError(s,
              $"{jumpStmt} is allowed only in contexts with {s.BreakAndContinueCount} enclosing loops, but the current context only has {loopStack.Count}");
          } else {
            var target = loopStack[^s.BreakAndContinueCount];
            if (!target.Labels.Any()) {
              // make sure there is a label, because the compiler and translator will want to see a unique ID
              target.Labels = [new Label(target.Origin, null)];
            }
            s.TargetStmt = target;
          }
        }

      } else if (stmt is ProduceStmt) {
        var kind = stmt is YieldStmt ? "yield" : "return";
        if (stmt is YieldStmt && !(resolutionContext.CodeContext is IteratorDecl)) {
          ReportError(stmt, "yield statement is allowed only in iterators");
        } else if (stmt is ReturnStmt && !(resolutionContext.CodeContext is MethodOrConstructor)) {
          ReportError(stmt, "return statement is allowed only in method");
        } else if (resolutionContext.InFirstPhaseConstructor) {
          ReportError(stmt, "return statement is not allowed before 'new;' in a constructor");
        }
        var s = (ProduceStmt)stmt;
        if (s.Rhss == null) {
          // this is a regular return/yield statement.
          s.HiddenUpdate = null;
        } else {
          var cmc = resolutionContext.AsMethodCodeContext;
          if (cmc == null) {
            // an error has already been reported above
          } else if (cmc.Outs.Count != s.Rhss.Count) {
            ReportError(s, "number of {2} parameters does not match declaration (found {0}, expected {1})", s.Rhss.Count, cmc.Outs.Count, kind);
          } else {
            Contract.Assert(s.Rhss.Count > 0);
            // Create a hidden update statement using the out-parameter formals, resolve the RHS, and check that the RHS is good.
            List<Expression> formals = [];
            foreach (Formal f in cmc.Outs) {
              Expression produceLhs;
              if (stmt is ReturnStmt) {
                var ident = new IdentifierExpr(f.Origin, f.Name);
                // resolve it here to avoid capture into more closely declared local variables
                Contract.Assert(f.Type != null);
                ident.Var = f;
                ident.PreType = Type2PreType(ident.Var.Type);
                produceLhs = ident;
              } else {
                var yieldIdent = new ExprDotName(f.Origin, new ImplicitThisExpr(f.Origin), new Name(f.Name), null);
                ResolveExpression(yieldIdent, resolutionContext);
                produceLhs = yieldIdent;
              }
              formals.Add(produceLhs);
            }
            s.HiddenUpdate = new AssignStatement(s.Origin, formals, s.Rhss, true);
            // resolving the update statement will check for return/yield statement specifics.
            ResolveStatement(s.HiddenUpdate, resolutionContext);
          }
        }

      } else if (stmt is ConcreteAssignStatement concreteUpdateStatement) {
        ResolveConcreteUpdateStmt(concreteUpdateStatement, null, resolutionContext);

      } else if (stmt is VarDeclStmt varDeclStmt) {
        ResolveConcreteUpdateStmt(varDeclStmt.Assign, varDeclStmt.Locals, resolutionContext);

      } else if (stmt is VarDeclPattern) {
        var s = (VarDeclPattern)stmt;
        foreach (var local in s.LocalVars) {
          int prevErrorCount = ErrorCount;
          resolver.ResolveType(local.Origin, local.SafeSyntacticType, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          local.type = ErrorCount == prevErrorCount ? local.type = local.SafeSyntacticType : new InferredTypeProxy();
          local.PreType = Type2PreType(local.type);
        }
        ResolveExpression(s.RHS, resolutionContext);
        ResolveCasePattern(s.LHS, s.RHS.PreType, resolutionContext);
        // Check for duplicate names now, because not until after resolving the case pattern do we know if identifiers inside it refer to bound variables or nullary constructors
        var c = 0;
        foreach (var bv in s.LHS.Vars) {
          ScopePushAndReport(scope, bv.Name, bv, bv.Origin, "local variable");
          c++;
        }
        if (c == 0) {
          // Every identifier-looking thing in the pattern resolved to a constructor; that is, this LHS is a constant literal
          ReportError(s.LHS.Origin, "LHS is a constant literal; to be legal, it must introduce at least one bound variable");
        }

      } else if (stmt is SingleAssignStmt) {
        var s = (SingleAssignStmt)stmt;
        int prevErrorCount = ErrorCount;
        ResolveExpression(s.Lhs, resolutionContext);  // allow ghosts for now, tightened up below
        bool lhsResolvedSuccessfully = ErrorCount == prevErrorCount;
        // check that LHS denotes a mutable variable or a field
        var lhs = s.Lhs.Resolved;
        if (lhs is IdentifierExpr) {
          IVariable var = ((IdentifierExpr)lhs).Var;
          if (var == null) {
            // the LHS didn't resolve correctly; some error would already have been reported
          } else {
            CheckIsLvalue(lhs, resolutionContext);
          }
        } else if (lhs is MemberSelectExpr mseLhs) {
          if (mseLhs.Member != null) {  // otherwise, an error was reported above
            CheckIsLvalue(mseLhs, resolutionContext);
          }
        } else if (lhs is SeqSelectExpr sseLhs) {
          // LHS is fine, provided the "sequence" is really an array
          if (lhsResolvedSuccessfully) {
            CheckIsLvalue(sseLhs, resolutionContext);
          }
        } else {
          CheckIsLvalue(lhs, resolutionContext);
        }
        var lhsPreType = s.Lhs.PreType;
        if (s.Rhs is ExprRhs) {
          var rr = (ExprRhs)s.Rhs;
          ResolveExpression(rr.Expr, resolutionContext);
          AddSubtypeConstraint(lhsPreType, rr.Expr.PreType, stmt.Origin, "RHS (of type {1}) not assignable to LHS (of type {0})");
        } else if (s.Rhs is TypeRhs) {
          var rr = (TypeRhs)s.Rhs;
          ResolveTypeRhs(rr, stmt, resolutionContext);
          AddSubtypeConstraint(lhsPreType, rr.PreType, stmt.Origin, "type {1} is not assignable to LHS (of type {0})");
        } else if (s.Rhs is HavocRhs havocRhs) {
          havocRhs.Resolve(this, resolutionContext);
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected RHS
        }

      } else if (stmt is CallStmt callStmt) {
        ResolveCallStmt(callStmt, resolutionContext, null);

      } else if (stmt is BlockStmt blockStmt) {
        scope.PushMarker();
        ResolveBlockStatement(blockStmt, resolutionContext);
        scope.PopMarker();

      } else if (stmt is IfStmt ifStmt) {
        ifStmt.Resolve(this, resolutionContext);
      } else if (stmt is AlternativeStmt) {
        var s = (AlternativeStmt)stmt;
        s.Resolve(this, resolutionContext);

      } else if (stmt is OneBodyLoopStmt oneBodyLoopStmt) {
        ResolveOneBodyLoopStmt(oneBodyLoopStmt, resolutionContext);

      } else if (stmt is AlternativeLoopStmt) {
        var s = (AlternativeLoopStmt)stmt;
        if (!resolutionContext.IsGhost && Options.ForbidNondeterminism) {
          Reporter.Error(MessageSource.Resolver, GeneratorErrors.ErrorId.c_case_based_loop_forbidden, s.Origin,
            "case-based loop forbidden by the --enforce-determinism option");
        }
        AlternativeStmt.ResolveAlternatives(this, s.Alternatives, s, resolutionContext);
        ResolveLoopSpecificationComponents(s.Invariants, s.Decreases, s.Mod, resolutionContext);

      } else if (stmt is ForallStmt) {
        var s = (ForallStmt)stmt;

        int prevErrorCount = ErrorCount;
        scope.PushMarker();
        foreach (BoundVar v in s.BoundVars) {
          resolver.ResolveType(v.Origin, v.Type, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          ScopePushAndReport(v, "local-variable");
        }
        ResolveExpression(s.Range, resolutionContext);
        ConstrainTypeExprBool(s.Range, "range restriction in forall statement must be of type bool (instead got {0})");
        foreach (var ens in s.Ens) {
          ResolveExpression(ens.E, resolutionContext);
          ConstrainTypeExprBool(ens.E, "ensures condition is expected to be of type bool, but is {0}");
        }
        // Since the range and postconditions are more likely to infer the types of the bound variables, resolve them
        // first (above) and only then resolve the attributes (below).
        ResolveAttributes(s, resolutionContext, false);

        if (s.Body != null) {
          // clear the labels for the duration of checking the body, because break statements are not allowed to leave a forall statement
          var prevLblStmts = EnclosingStatementLabels;
          var prevLoopStack = loopStack;
          EnclosingStatementLabels = new Scope<LabeledStatement>(resolver.Options);
          loopStack = [];
          ResolveStatement(s.Body, resolutionContext);
          EnclosingStatementLabels = prevLblStmts;
          loopStack = prevLoopStack;
        }
        scope.PopMarker();

        if (prevErrorCount == ErrorCount) {
          // determine the Kind and run some additional checks on the body
          if (s.Ens.Count != 0) {
            // The only supported kind with ensures clauses is Proof.
            s.Kind = ForallStmt.BodyKind.Proof;
          } else {
            // There are three special cases:
            // * Assign, which is the only kind of the forall statement that allows a heap update.
            // * Call, which is a single call statement with no side effects or output parameters.
            // * A single calc statement, which is a special case of Proof where the postcondition can be inferred.
            // The effect of Assign and the postcondition of Call will be seen outside the forall
            // statement.
            Statement s0 = s.S0;
            if (s0 is SingleAssignStmt) {
              s.Kind = ForallStmt.BodyKind.Assign;

              var rhs = ((SingleAssignStmt)s0).Rhs;
              if (rhs is TypeRhs) {
                ReportError(rhs.Origin, "new allocation not supported in aggregate assignments");
              }

            } else if (s0 is CallStmt) {
              s.Kind = ForallStmt.BodyKind.Call;
              var call = (CallStmt)s.S0;
              var method = call.Method;
              // if the called method is not in the same module as the ForallCall stmt
              // don't convert it to ForallExpression since the inlined called method's
              // ensure clause might not be resolved correctly(test\dafny3\GenericSort.dfy)
              if (method.EnclosingClass.EnclosingModuleDefinition != resolutionContext.CodeContext.EnclosingModule) {
                s.CanConvert = false;
              }
              // Additional information (namely, the postcondition of the call) will be reported later. But it cannot be
              // done yet, because the specification of the callee may not have been resolved yet.
            } else if (s0 is CalcStmt) {
              s.Kind = ForallStmt.BodyKind.Proof;
              // add the conclusion of the calc as a free postcondition
              var result = ((CalcStmt)s0).Result;
              s.Ens.Add(new AttributedExpression(result));
              ReportInfo(s.Origin, "ensures " + Printer.ExprToString(resolver.Options, result));
            } else {
              s.Kind = ForallStmt.BodyKind.Proof;
              if (s.Body is BlockStmt && ((BlockStmt)s.Body).Body.Count == 0) {
                // an empty statement, so don't produce any warning
              } else {
                ReportWarning(s.Origin, "the conclusion of the body of this forall statement will not be known outside the forall statement; consider using an 'ensures' clause");
              }
            }
          }

          if (s.EffectiveEnsuresClauses != null) {
            foreach (Expression expr in s.EffectiveEnsuresClauses) {
              ResolveExpression(expr, resolutionContext);
            }
          }
        }

      } else if (stmt is ModifyStmt modifyStmt) {
        if (modifyStmt.Body == null) {
          if (!resolutionContext.IsGhost && Options.ForbidNondeterminism) {
            Reporter.Error(MessageSource.Resolver, GeneratorErrors.ErrorId.c_bodyless_modify_statement_forbidden,
              modifyStmt.Origin, "modify statement without a body forbidden by the --enforce-determinism option");
          }
        }
        ResolveAttributes(modifyStmt.Mod, resolutionContext, false);
        foreach (FrameExpression fe in modifyStmt.Mod.Expressions) {
          ResolveFrameExpression(fe, FrameExpressionUse.Modifies, resolutionContext.CodeContext);
        }
        if (modifyStmt.Body != null) {
          ResolveBlockStatement(modifyStmt.Body, resolutionContext);
        }

      } else if (stmt is CalcStmt calcStmt) {
        ResolveCalc(calcStmt, resolutionContext);

      } else if (stmt is MatchStmt matchStmt) {
        Contract.Assert(false); // a plain MatchStmt isn't introduced until post-resolution

      } else if (stmt is NestedMatchStmt nestedMatchStmt) {
        ResolveNestedMatchStmt(nestedMatchStmt, resolutionContext);

      } else if (stmt is SkeletonStatement skeletonStatement) {
        ReportError(stmt.Origin, "skeleton statements are allowed only in refining methods");
        // nevertheless, resolve the underlying statement; hey, why not
        if (skeletonStatement.S != null) {
          ResolveStatement(skeletonStatement.S, resolutionContext);
        }

      } else if (stmt is LabeledStatement) {
        // content already handled 
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();
      }
    }

    private void ResolveOneBodyLoopStmt(OneBodyLoopStmt s, ResolutionContext resolutionContext) {
      Contract.Requires(s != null);
      Contract.Requires(resolutionContext != null);

      if (s is WhileStmt whileS) {
        if (whileS.Guard != null) {
          ResolveExpression(whileS.Guard, resolutionContext);
          ConstrainTypeExprBool(whileS.Guard, "condition is expected to be of type bool, but is {0}");
        } else {
          if (!resolutionContext.IsGhost && Options.ForbidNondeterminism) {
            Reporter.Error(MessageSource.Resolver, GeneratorErrors.ErrorId.c_non_deterministic_loop_forbidden, s.Origin,
              "nondeterministic loop forbidden by the --enforce-determinism option");
          }
        }
      }
      if (s is ForLoopStmt forS) {
        var loopIndex = forS.LoopIndex;
        resolver.ResolveType(loopIndex.Origin, loopIndex.Type, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
        loopIndex.PreType = Type2PreType(loopIndex.Type);
        AddConfirmation(PreTypeConstraints.CommonConfirmationBag.InIntFamily, loopIndex.PreType, loopIndex.Origin, "index variable is expected to be of an integer type (got {0})");

        ResolveExpression(forS.Start, resolutionContext);
        AddSubtypeConstraint(loopIndex.PreType, forS.Start.PreType, forS.Start.Origin,
          "lower bound (of type {1}) not assignable to index variable (of type {0})");
        if (forS.End != null) {
          ResolveExpression(forS.End, resolutionContext);
          AddSubtypeConstraint(loopIndex.PreType, forS.End.PreType, forS.End.Origin,
            "upper bound (of type {1}) not assignable to index variable (of type {0})");
          if (forS.Decreases.Expressions.Count != 0) {
            ReportError(forS.Decreases.Expressions[0].Origin,
              "a 'for' loop is allowed an explicit 'decreases' clause only if the end-expression is '*'");
          }
        } else if (forS.Decreases.Expressions.Count == 0 && !resolutionContext.CodeContext.AllowsNontermination) {
          // note, the following error message is also emitted elsewhere (if the loop bears a "decreases *")
          ReportError(forS.Origin,
            "a possibly infinite loop is allowed only if the enclosing method is declared (with 'decreases *') to be possibly non-terminating" +
            " (or you can add a 'decreases' clause to this 'for' loop if you want to prove that it does indeed terminate)");
        }

        // Create a new scope, add the local to the scope, and resolve the attributes
        scope.PushMarker();
        ScopePushAndReport(loopIndex, "index-variable", false);
        ResolveAttributes(s, resolutionContext, false);
      }

      ResolveLoopSpecificationComponents(s.Invariants, s.Decreases, s.Mod, resolutionContext);

      if (s.Body != null) {
        loopStack.Add(s); // push
        DominatingStatementLabels.PushMarker();
        ResolveStatement(s.Body, resolutionContext);
        DominatingStatementLabels.PopMarker();
        loopStack.RemoveAt(loopStack.Count - 1); // pop
      }

      if (s is ForLoopStmt) {
        scope.PopMarker();
      }
    }

    private void ResolveCalc(CalcStmt s, ResolutionContext resolutionContext) {
      var prevErrorCount = ErrorCount;
      // figure out s.Op
      Contract.Assert(s.Op == null); // it hasn't been set yet
      if (s.UserSuppliedOp != null) {
        s.Op = s.UserSuppliedOp;
      } else {
        s.Op = s.GetInferredDefaultOp() ?? CalcStmt.DefaultOp;
        ReportInfo(s.Origin, s.Op.ToString());
      }

      if (s.Lines.Count > 0) {
        PreType linePreType = CreatePreTypeProxy("calc line");
        var e0 = s.Lines.First();
        ResolveExpression(e0, resolutionContext);
        AddSubtypeConstraint(linePreType, e0.PreType, e0.Origin, "all lines in a calculation must have the same type (got {1} after {0})");
        for (var i = 1; i < s.Lines.Count; i++) {
          var e1 = s.Lines[i];
          ResolveExpression(e1, resolutionContext);
#if SOON
          // reuse the error object if we're on the dummy line; this prevents a duplicate error message
#endif
          if (i < s.Lines.Count - 1) {
            AddSubtypeConstraint(linePreType, e1.PreType, e1.Origin, "all lines in a calculation must have the same type (got {1} after {0})");
          }
          var step = (s.StepOps[i - 1] ?? s.Op).StepExpr(e0, e1); // Use custom line operator
          ResolveExpression(step, resolutionContext);
          s.Steps.Add(step);
          e0 = e1;
        }

        // clear the labels for the duration of checking the hints, because break statements are not allowed to leave a forall statement
        var prevLblStmts = EnclosingStatementLabels;
        var prevLoopStack = loopStack;
        EnclosingStatementLabels = new Scope<LabeledStatement>(resolver.Options);
        loopStack = [];
        foreach (var h in s.Hints) {
          foreach (var oneHint in h.Body) {
            DominatingStatementLabels.PushMarker();
            ResolveStatement(oneHint, resolutionContext);
            DominatingStatementLabels.PopMarker();
          }
        }
        EnclosingStatementLabels = prevLblStmts;
        loopStack = prevLoopStack;
      }
      if (prevErrorCount == ErrorCount && s.Lines.Count > 0) {
        // do not build Result from the lines if there were errors, as it might be ill-typed and produce unnecessary resolution errors
        var resultOp = s.StepOps.Aggregate(s.Op, (op0, op1) => op1 == null ? op0 : op0.ResultOp(op1));
        s.Result = resultOp.StepExpr(s.Lines.First(), s.Lines.Last());
      } else {
        s.Result = CalcStmt.DefaultOp.StepExpr(Expression.CreateIntLiteral(s.Origin, 0), Expression.CreateIntLiteral(s.Origin, 0));
      }
      ResolveExpression(s.Result, resolutionContext);
      Contract.Assert(s.Result != null);
      Contract.Assert(prevErrorCount != ErrorCount || s.Steps.Count == s.Hints.Count);
    }

    private void ResolveConcreteUpdateStmt(ConcreteAssignStatement assign, List<LocalVariable> locals, ResolutionContext resolutionContext) {
      Contract.Requires(assign != null || locals != null);
      // We have four cases.
      Contract.Assert(assign is null or AssignSuchThatStmt or AssignStatement or AssignOrReturnStmt);
      // 0.  There is no update.  This is easy, we will just resolve the locals.
      // 1.  The update is an AssignSuchThatStmt.  This is also straightforward:  first
      //     resolve the locals, which adds them to the scope, and then resolve the update.
      // 2.  The update is an UpdateStmt, which, resolved, means either a CallStmt or a bunch
      //     of simultaneous AssignStmt's.  Here, the right-hand sides should be resolved before
      //     the local variables have been added to the scope, but the left-hand sides should
      //     resolve to the newly introduced variables.
      // 3.  The update is a ":-" statement, for which resolution does two steps:
      //     First, desugar, then run the regular resolution on the desugared AST.

      var errorCountBeforeCheckingStmt = ErrorCount;

      // For UpdateStmt and AssignOrReturnStmt, resolve the RHSs before adding the LHSs to the scope
      if (assign is AssignStatement updateStatement) {
        foreach (var rhs in updateStatement.Rhss) {
          ResolveAssignmentRhs(rhs, updateStatement, resolutionContext);
        }
      } else if (assign is AssignOrReturnStmt elephantStmt) {
        elephantStmt.ResolveKeywordToken(this, resolutionContext);

        ResolveAssignmentRhs(elephantStmt.Rhs, elephantStmt, resolutionContext);
        if (elephantStmt.Rhss != null) {
          foreach (var rhs in elephantStmt.Rhss) {
            ResolveAssignmentRhs(rhs, elephantStmt, resolutionContext);
          }
        }
      }

      if (locals != null) {
        // Add the locals to the scope
        foreach (var local in locals) {
          int prevErrorCount = ErrorCount;
          resolver.ResolveType(local.Origin, local.SafeSyntacticType, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          local.type = ErrorCount == prevErrorCount ? local.SafeSyntacticType : new InferredTypeProxy();
          ScopePushAndReport(local, "local-variable", true);
        }
        // With the new locals in scope, it's now time to resolve the attributes on all the locals
        foreach (var local in locals) {
          ResolveAttributes(local, resolutionContext, false);
        }
      }

      if (assign is AssignSuchThatStmt assignSuchThatStmt) {
        assignSuchThatStmt.GenResolve(this, resolutionContext);
      } else {
        // Resolve the LHSs
        if (assign != null) {
          foreach (var lhs in assign.Lhss) {
            ResolveExpression(lhs, resolutionContext);
          }
        }

        if (assign is AssignStatement updateStmt) {
          ResolveUpdateStmt(updateStmt, resolutionContext, errorCountBeforeCheckingStmt);
        } else if (assign is AssignOrReturnStmt assignOrReturnStmt) {
          ResolveAssignOrReturnStmt(assignOrReturnStmt, resolutionContext);
        } else {
          Contract.Assert(assign == null);
        }
      }
    }

    void ResolveAssignmentRhs(AssignmentRhs rhs, Statement enclosingStmt, ResolutionContext resolutionContext) {
      Contract.Requires(rhs != null);
      Contract.Requires(enclosingStmt != null);
      Contract.Requires(resolutionContext != null);

      if (rhs is TypeRhs tr) {
        ResolveTypeRhs(tr, enclosingStmt, resolutionContext);
      } else if (rhs is ExprRhs er) {
        if (er.Expr is ApplySuffix applySuffix) {
          ResolveApplySuffix(applySuffix, resolutionContext, true);
        } else {
          ResolveExpression(er.Expr, resolutionContext);
        }
      } else {
        Contract.Assert(rhs is HavocRhs);
      }

      ResolveAttributes(rhs, resolutionContext, false);
    }

    /// <summary>
    /// Assumes that LHSs and RHSs have already been resolved.
    /// Resolve the entire UpdateStmt.
    /// errorCountBeforeCheckingStmt is passed in so that this method can determine if any resolution errors were found during
    /// LHS or RHS checking, because only if no errors were found is update.ResolvedStmt changed.
    /// </summary>
    private void ResolveUpdateStmt(AssignStatement update, ResolutionContext resolutionContext,
      int errorCountBeforeCheckingStmt) {
      Contract.Requires(update != null);
      Contract.Requires(resolutionContext != null);
      IOrigin firstEffectfulRhs = null;
      MethodCallInformation methodCallInfo = null;
      update.ResolvedStatements = [];
      foreach (var rhs in update.Rhss) {
        bool isEffectful;
        if (rhs is AllocateClass tr) {
          isEffectful = tr.InitCall != null;
        } else if (rhs is HavocRhs) {
          isEffectful = false;
        } else if (rhs is ExprRhs er) {
          if (er.Expr is ApplySuffix applySuffix) {
            var cRhs = applySuffix.MethodCallInfo;
            isEffectful = cRhs != null;
            methodCallInfo ??= cRhs;
          } else {
            isEffectful = false;
          }
        } else {
          isEffectful = false;
        }

        if (isEffectful && firstEffectfulRhs == null) {
          firstEffectfulRhs = rhs.Origin;
        }
      }

      // figure out what kind of UpdateStmt this is
      if (firstEffectfulRhs == null) {
        if (update.Lhss.Count == 0) {
          Contract.Assert(update.Rhss.Count == 1); // guaranteed by the parser
          ReportError(update, "expected method call, found expression");
        } else if (update.Lhss.Count != update.Rhss.Count) {
          ReportError(update,
            "the number of left-hand sides ({0}) and right-hand sides ({1}) must match for a multi-assignment",
            update.Lhss.Count, update.Rhss.Count);
        } else if (ErrorCount == errorCountBeforeCheckingStmt) {
          // add the statements here in a sequence, but don't use that sequence later for translation (instead, should translate properly as multi-assignment)
          for (var i = 0; i < update.Lhss.Count; i++) {
            var a = new SingleAssignStmt(update.Origin, update.Lhss[i].Resolved, update.Rhss[i]);
            update.ResolvedStatements.Add(a);
          }
        }

      } else if (update.CanMutateKnownState) {
        if (1 < update.Rhss.Count) {
          ReportError(firstEffectfulRhs, "cannot have effectful parameter in multi-return statement.");
        } else {
          // it might be ok, if it is a TypeRhs
          Contract.Assert(update.Rhss.Count == 1);
          if (methodCallInfo != null) {
            ReportError(methodCallInfo.Tok, "cannot have method call in return statement.");
          } else {
            // we have a TypeRhs
            var tr = (AllocateClass)update.Rhss[0];
            Contract.Assert(tr.InitCall != null); // there were effects, so this must have been a call.
            if (tr.CanAffectPreviouslyKnownExpressions) {
              ReportError(tr.Origin, "can only have initialization methods which modify at most 'this'.");
            } else if (ErrorCount == errorCountBeforeCheckingStmt) {
              var a = new SingleAssignStmt(update.Origin, update.Lhss[0].Resolved, tr);
              update.ResolvedStatements.Add(a);
            }
          }
        }

      } else {
        // if there was an effectful RHS, that must be the only RHS
        if (update.Rhss.Count != 1) {
          ReportError(firstEffectfulRhs,
            "an update statement is allowed an effectful RHS only if there is just one RHS");
        } else if (methodCallInfo == null) {
          // must be a single TypeRhs
          if (update.Lhss.Count != 1) {
            Contract.Assert(2 <=
                            update.Lhss
                              .Count); // the parser allows 0 Lhss only if the whole statement looks like an expression (not a TypeRhs)
            ReportError(update.Lhss[1].Origin,
              "the number of left-hand sides ({0}) and right-hand sides ({1}) must match for a multi-assignment",
              update.Lhss.Count, update.Rhss.Count);
          } else if (ErrorCount == errorCountBeforeCheckingStmt) {
            var a = new SingleAssignStmt(update.Origin, update.Lhss[0].Resolved, update.Rhss[0]);
            update.ResolvedStatements.Add(a);
          }
        } else if (ErrorCount == errorCountBeforeCheckingStmt) {
          // a call statement
          var resolvedLhss = update.Lhss.ConvertAll(ll => ll.Resolved);
          var a = new CallStmt(update.Origin, resolvedLhss, methodCallInfo.Callee, methodCallInfo.ActualParameters, methodCallInfo.Tok.ReportingRange);
          a.OriginalInitialLhs = update.OriginalInitialLhs;
          update.ResolvedStatements.Add(a);
        }
      }

      foreach (var a in update.ResolvedStatements) {
        ResolveStatement(a, resolutionContext);
      }
    }

    private void ResolveLoopSpecificationComponents(List<AttributedExpression> invariants,
      Specification<Expression> decreases, Specification<FrameExpression> modifies,
      ResolutionContext resolutionContext) {
      Contract.Requires(invariants != null);
      Contract.Requires(decreases != null);
      Contract.Requires(modifies != null);
      Contract.Requires(resolutionContext != null);

      foreach (AttributedExpression inv in invariants) {
        ResolveAttributes(inv, resolutionContext, false);
        ResolveExpression(inv.E, resolutionContext);
        ConstrainTypeExprBool(inv.E, "invariant is expected to be of type bool, but is {0}");
      }

      ResolveAttributes(decreases, resolutionContext, false);
      foreach (Expression e in decreases.Expressions) {
        ResolveExpression(e, resolutionContext);
        if (e is WildcardExpr && !resolutionContext.CodeContext.AllowsNontermination) {
          ReportError(e, "a possibly infinite loop is allowed only if the enclosing method is declared (with 'decreases *') to be possibly non-terminating");
        }
        // any type is fine
      }

      ResolveAttributes(modifies, resolutionContext, false);
      if (modifies.Expressions != null) {
        foreach (var fe in modifies.Expressions) {
          ResolveFrameExpression(fe, FrameExpressionUse.Modifies, resolutionContext.CodeContext);
        }
      }
    }

    /// <summary>
    /// Resolves the given call statement.
    /// Assumes all LHSs have already been resolved (and checked for mutability).
    /// </summary>
    void ResolveCallStmt(CallStmt s, ResolutionContext resolutionContext, Type receiverType) {
      Contract.Requires(s != null);
      Contract.Requires(resolutionContext != null);
      bool isInitCall = receiverType != null;

      var callee = s.Method;
      Contract.Assert(callee != null);  // follows from the invariant of CallStmt
      if (!isInitCall && callee is Constructor) {
        ReportError(s, "a constructor is allowed to be called only when an object is being allocated");
      }

      // resolve left-hand sides (the right-hand sides are resolved below)
      foreach (var lhs in s.Lhs) {
        Contract.Assume(lhs.PreType != null);  // a sanity check that LHSs have already been resolved
      }

      bool tryToResolve = false;
      if (callee.Outs.Count != s.Lhs.Count) {
        if (isInitCall) {
          ReportError(s, "a method called as an initialization method must not have any result arguments");
        } else {
          ReportError(s, "wrong number of method result arguments (got {0}, expected {1})", s.Lhs.Count, callee.Outs.Count);
          tryToResolve = true;
        }
      } else {
        if (isInitCall) {
          if (callee.IsStatic) {
            ReportError(s.Origin, "a method called as an initialization method must not be 'static'");
          } else {
            tryToResolve = true;
          }
        } else if (!callee.IsStatic) {
          if (!scope.AllowInstance && s.Receiver is ThisExpr) {
            // The call really needs an instance, but that instance is given as 'this', which is not
            // available in this context.  For more details, see comment in the resolution of a
            // FunctionCallExpr.
            ReportError(s.Receiver, "'this' is not allowed in a 'static' context");
          } else if (s.Receiver is StaticReceiverExpr) {
            ReportError(s.Receiver, "call to instance method requires an instance");
          } else {
            tryToResolve = true;
          }
        } else {
          tryToResolve = true;
        }
      }

      if (tryToResolve) {
        var typeMap = s.MethodSelect.PreTypeArgumentSubstitutionsAtMemberDeclaration();
        AddTypeBoundConstraints(s.Origin, callee.EnclosingClass.TypeArgs, typeMap);
        AddTypeBoundConstraints(s.Origin, callee.TypeArgs, typeMap);
        // resolve arguments
        ResolveActualParameters(s.Bindings, callee.Ins, s.Origin, callee, resolutionContext, typeMap,
          callee.IsStatic ? null : s.Receiver);
        // type check the out-parameter arguments (in-parameters were type checked as part of ResolveActualParameters)
        for (var i = 0; i < callee.Outs.Count && i < s.Lhs.Count; i++) {
          var outFormal = callee.Outs[i];
          var st = outFormal.PreType.Substitute(typeMap);
          var lhs = s.Lhs[i];
          var what = GetLocationInformation(outFormal, callee.Outs.Count, i, "method out-parameter");

          AddSubtypeConstraint(lhs.PreType, st, s.Origin, $"incorrect return type {what} (expected {{1}}, got {{0}})");
        }
        for (int i = 0; i < s.Lhs.Count; i++) {
          var lhs = s.Lhs[i];
          // LHS must denote a mutable field.
          CheckIsLvalue(lhs.Resolved, resolutionContext);
        }

      }
      if (Contract.Exists(callee.Decreases.Expressions, e => e is WildcardExpr) && !resolutionContext.CodeContext.AllowsNontermination) {
        ReportError(s.Origin, "a call to a possibly non-terminating method is allowed only if the calling method is also declared (with 'decreases *') to be possibly non-terminating");
      }
    }

    /// <summary>
    /// Desugars "y, ... :- MethodOrExpression" into
    /// var temp;
    /// temp, ... := MethodOrExpression;
    /// if temp.IsFailure() { return temp.PropagateFailure(); }
    /// y := temp.Extract();
    ///
    /// If the type of MethodExpression does not have an Extract, then the desugaring is
    /// var temp;
    /// temp, y, ... := MethodOrExpression;
    /// if temp.IsFailure() { return temp.PropagateFailure(); }
    ///
    /// If there are multiple RHSs then "y, ... :- Expression, ..." becomes
    /// var temp;
    /// temp, ... := Expression, ...;
    /// if temp.IsFailure() { return temp.PropagateFailure(); }
    /// y := temp.Extract();
    /// OR
    /// var temp;
    /// temp, y, ... := Expression, ...;
    /// if temp.IsFailure() { return temp.PropagateFailure(); }
    ///
    /// and "y, ... :- expect MethodOrExpression, ..." into
    /// var temp, [y, ] ... := MethodOrExpression, ...;
    /// expect !temp.IsFailure(), temp.PropagateFailure();
    /// [y := temp.Extract();]
    ///
    /// and saves the result into s.ResolvedStatements.
    /// This is also known as the "elephant operator"
    /// </summary>
    private void ResolveAssignOrReturnStmt(AssignOrReturnStmt s, ResolutionContext resolutionContext) {
      // We need to figure out whether we are using a status type that has Extract or not,
      // as that determines how the AssignOrReturnStmt is desugared. Thus if the RHS is a
      // method call, then we need to know which one (to inspect its first output); if RHS is a
      // list of expressions, we need to know the type of the first one. For all of this we have
      // to do some partial type resolution.

      bool expectExtract = s.Lhss.Count != 0; // default value if we cannot determine and inspect the type
      PreType firstPreType = null;
      MethodOrConstructor callee = null;
      Contract.Assert(s.Rhss != null);
      if (s.Rhss.Count == 0 && s.Rhs.Expr is ApplySuffix asx) {
        var methodCallInfo = ResolveApplySuffix(asx, resolutionContext, true);
        callee = methodCallInfo?.Callee.Member as MethodOrConstructor;
        if (callee != null) {
          // We're looking at a method call
          if (callee.Outs.Count != 0) {
            var typeMap = PreType.PreTypeSubstMap(callee.TypeArgs, methodCallInfo.Callee.PreTypeApplicationJustMember);
            firstPreType = callee.Outs[0].PreType.Substitute(typeMap);
          } else {
            ReportError(s.Rhs.Origin, $"Expected '{callee.Name}' to have a success/failure output value, but the method returns nothing.");
          }
        } else {
          // We're looking at a call to a function. Treat it like any other expression.
          firstPreType = asx.PreType;
        }
      } else {
        ResolveExpression(s.Rhs.Expr, resolutionContext);
        firstPreType = s.Rhs.Expr.PreType;
      }

      var enclosingMethod = (MethodOrConstructor)resolutionContext.CodeContext;
      if (enclosingMethod.Outs.Count == 0 && s.KeywordToken == null) {
        ReportError(s.Origin, $"A method containing a :- statement must have an out-parameter ({enclosingMethod.Name})");
        return;
      }
      TopLevelDeclWithMembers failureSupportingType = null;
      if (firstPreType != null) {
        Constraints.FindDefinedPreType(firstPreType, true);
        failureSupportingType = (firstPreType.Normalize() as DPreType)?.Decl as TopLevelDeclWithMembers;
        if (failureSupportingType != null) {
          if (failureSupportingType.Members.Find(x => x.Name == "IsFailure") == null) {
            ReportError(s.Origin, $"member IsFailure does not exist in {firstPreType}, in :- statement");
            return;
          }
          expectExtract = failureSupportingType.Members.Find(x => x.Name == "Extract") != null;
          if (expectExtract && callee == null && s.Lhss.Count != 1 + s.Rhss.Count) {
            ReportError(s.Origin,
              "number of lhs ({0}) must match number of rhs ({1}) for a rhs type ({2}) with member Extract",
              s.Lhss.Count, 1 + s.Rhss.Count, firstPreType);
            return;
          } else if (expectExtract && callee != null && s.Lhss.Count != callee.Outs.Count) {
            ReportError(s.Origin,
              "wrong number of method result arguments (got {0}, expected {1}) for a rhs type ({2}) with member Extract",
              s.Lhss.Count, callee.Outs.Count, firstPreType);
            return;
          } else if (!expectExtract && callee == null && s.Lhss.Count != s.Rhss.Count) {
            ReportError(s.Origin, "number of lhs ({0}) must be one less than number of rhs ({1}) for a rhs type ({2}) without member Extract",
              s.Lhss.Count, 1 + s.Rhss.Count, firstPreType);
            return;
          } else if (!expectExtract && callee != null && s.Lhss.Count != callee.Outs.Count - 1) {
            ReportError(s.Origin, "wrong number of method result arguments (got {0}, expected {1}) for a rhs type ({2}) without member Extract",
              s.Lhss.Count, callee.Outs.Count - 1, firstPreType);
            return;
          }
        } else {
          ReportError(s.Origin,
            $"The type of the first expression to the right of ':-' could not be determined to be a failure type (got '{firstPreType}')");
          return;
        }
      } else {
        ReportError(s.Origin, "Internal Error: Unknown failure type in :- statement");
        return;
      }

      Expression lhsExtract = null;
      if (expectExtract) {
        if (enclosingMethod.Outs.Count == 0 && s.KeywordToken == null) {
          ReportError(s.Rhs.Origin, $"Expected {enclosingMethod.Name} to have a Success/Failure output value");
          return;
        }

        lhsExtract = s.Lhss[0];
        var lhsResolved = lhsExtract.Resolved;
        // Make a new unresolved expression
        if (lhsResolved is MemberSelectExpr lexr) {
          Expression id = Expression.AsThis(lexr.Obj) != null ? lexr.Obj : resolver.makeTemp("recv", s, resolutionContext, lexr.Obj);
          var lex = lhsExtract as ExprDotName; // might be just a NameSegment
          lhsExtract = new ExprDotName(lexr.Origin, id, lexr.MemberNameNode, lex?.OptTypeArguments);
        } else if (lhsResolved is SeqSelectExpr lseq) {
          if (!lseq.SelectOne || lseq.E0 == null) {
            ReportError(s.Origin, "Element ranges not allowed as l-values");
            return;
          }
          Expression id = resolver.makeTemp("recv", s, resolutionContext, lseq.Seq);
          Expression id0 = id0 = resolver.makeTemp("idx", s, resolutionContext, lseq.E0);
          lhsExtract = new SeqSelectExpr(lseq.Origin, lseq.SelectOne, id, id0, null, lseq.CloseParen);
          lhsExtract.Type = lseq.Type;
        } else if (lhsResolved is MultiSelectExpr lmulti) {
          Expression id = resolver.makeTemp("recv", s, resolutionContext, lmulti.Array);
          var idxs = new List<Expression>();
          foreach (var i in lmulti.Indices) {
            Expression idx = resolver.makeTemp("idx", s, resolutionContext, i);
            idxs.Add(idx);
          }
          lhsExtract = new MultiSelectExpr(lmulti.Origin, id, idxs);
          lhsExtract.Type = lmulti.Type;
        } else if (lhsResolved is IdentifierExpr) {
          // do nothing
        } else if (lhsResolved == null) {
          // LHS failed to resolve. Abort trying to resolve assign or return stmt
          return;
        } else {
          throw new InvalidOperationException("Internal error: unexpected option in AssignOrReturnStmt.Resolve");
        }
      }
      var temp = resolver.FreshTempVarName("valueOrError", resolutionContext.CodeContext);
      var lhss = new List<LocalVariable>() { new LocalVariable(s.Origin, temp, new InferredTypeProxy(), false) };
      // "var temp ;"
      s.ResolvedStatements.Add(new VarDeclStmt(s.Origin, lhss, null));
      var lhss2 = new List<Expression>() { new IdentifierExpr(s.Origin, temp) };
      for (int k = (expectExtract ? 1 : 0); k < s.Lhss.Count; ++k) {
        lhss2.Add(s.Lhss[k]);
      }
      List<AssignmentRhs> rhss2 = [s.Rhs];
      rhss2.AddRange(s.Rhss);
      if (s.Rhss.Count > 0) {
        if (lhss2.Count != rhss2.Count) {
          ReportError(s.Origin, "Mismatch in expected number of LHSs and RHSs");
          if (lhss2.Count < rhss2.Count) {
            rhss2.RemoveRange(lhss2.Count, rhss2.Count - lhss2.Count);
          } else {
            lhss2.RemoveRange(rhss2.Count, lhss2.Count - rhss2.Count);
          }
        }
      }
      // " temp, ... := MethodOrExpression, ...;"
      var up = new AssignStatement(s.Origin, lhss2, rhss2);
      if (expectExtract) {
        up.OriginalInitialLhs = s.Lhss.Count == 0 ? null : s.Lhss[0];
      }
      s.ResolvedStatements.Add(up);

      if (s.KeywordToken != null) {
        var keyword = s.KeywordToken.Token;
        var notFailureExpr = new UnaryOpExpr(keyword, UnaryOpExpr.Opcode.Not, resolver.VarDotMethod(s.Origin, temp, "IsFailure"));
        Statement ss = null;
        if (keyword.val == "expect") {
          // "expect !temp.IsFailure(), temp"
          ss = new ExpectStmt(new SourceOrigin(keyword, s.EndToken), notFailureExpr, new IdentifierExpr(s.Origin, temp), s.KeywordToken.Attrs);
        } else if (s.KeywordToken.Token.val == "assume") {
          ss = new AssumeStmt(new SourceOrigin(keyword, s.EndToken), notFailureExpr, SystemModuleManager.AxiomAttribute(s.KeywordToken.Attrs));
        } else if (s.KeywordToken.Token.val == "assert") {
          ss = new AssertStmt(new SourceOrigin(keyword, s.EndToken), notFailureExpr, null, s.KeywordToken.Attrs);
        } else {
          Contract.Assert(false, $"Invalid token in :- statement: {keyword.val}");
        }
        s.ResolvedStatements.Add(ss);
      } else {
        var enclosingOutParameter = ((MethodOrConstructor)resolutionContext.CodeContext).Outs[0];
        var ident = new IdentifierExpr(s.Origin, enclosingOutParameter.Name) {
          // resolve it here to avoid capture into more closely declared local variables
          Var = enclosingOutParameter,
          Type = enclosingOutParameter.Type,
          PreType = enclosingOutParameter.PreType
        };

        s.ResolvedStatements.Add(
          // "if temp.IsFailure()"
          new IfStmt(s.Origin, false, resolver.VarDotMethod(s.Origin, temp, "IsFailure"),
            // THEN: { out := temp.PropagateFailure(); return; }
            new BlockStmt(s.Origin, [
              new AssignStatement(s.Origin,
                [ident],
                [new ExprRhs(resolver.VarDotMethod(s.Origin, temp, "PropagateFailure"))]
              ),

              new ReturnStmt(s.Origin, null)

            ]),
            // ELSE: no else block
            null
          ));
      }

      if (expectExtract) {
        // "y := temp.Extract();"
        var lhs = s.Lhss[0];
        s.ResolvedStatements.Add(
          new AssignStatement(s.Origin,
            [lhsExtract],
            [new ExprRhs(resolver.VarDotMethod(s.Origin, temp, "Extract"))]
          ));
      }

      s.ResolvedStatements.ForEach(a => ResolveStatement(a, resolutionContext));
      EnsureSupportsErrorHandling(s.Origin, failureSupportingType, expectExtract, s.KeywordToken?.Token.val);
    }

    private void EnsureSupportsErrorHandling(IOrigin tok, TopLevelDeclWithMembers failureSupportingType, bool expectExtract, [CanBeNull] string keyword) {

      var isFailure = failureSupportingType.Members.Find(x => x.Name == "IsFailure");
      var propagateFailure = failureSupportingType.Members.Find(x => x.Name == "PropagateFailure");
      var extract = failureSupportingType.Members.Find(x => x.Name == "Extract");

      if (keyword != null) {
        if (isFailure == null || (extract != null) != expectExtract) {
          // more details regarding which methods are missing have already been reported by regular resolution
          var requiredMembers = expectExtract
            ? "functions 'IsFailure()' and 'Extract()'"
            : "function 'IsFailure()', but not 'Extract()'";
          ReportError(tok, $"The right-hand side of ':- {keyword}', which is of type '{failureSupportingType}', must have {requiredMembers}");
        }
      } else {
        if (isFailure == null || propagateFailure == null || (extract != null) != expectExtract) {
          // more details regarding which methods are missing have already been reported by regular resolution
          var requiredMembers = expectExtract
            ? "functions 'IsFailure()', 'PropagateFailure()', and 'Extract()'"
            : "functions 'IsFailure()' and 'PropagateFailure()', but not 'Extract()'";
          ReportError(tok, $"The right-hand side of ':-', which is of type '{failureSupportingType}', must have {requiredMembers}");
        }
      }

      void CheckIsFunction([CanBeNull] MemberDecl memberDecl, bool allowMethod) {
        if (memberDecl is null or Function) {
          // fine
        } else if (allowMethod && memberDecl is MethodOrConstructor) {
          // give a deprecation warning, so we will remove this language feature around the Dafny 4 time frame
          resolver.reporter.Deprecated(MessageSource.Resolver, ResolutionErrors.ErrorId.r_failure_methods_deprecated, tok,
            $"Support for member '{memberDecl.Name}' in type '{failureSupportingType}' (used indirectly via a :- statement) being a method is deprecated;" +
            " declare it to be a function instead");
        } else {
          // not allowed
          resolver.reporter.Error(MessageSource.Resolver, tok,
            $"Member '{memberDecl.Name}' in type '{failureSupportingType}' (used indirectly via a :- statement) is expected to be a function");
        }
      }

      CheckIsFunction(isFailure, false);
      if (keyword == null) {
        CheckIsFunction(propagateFailure, true);
      }
      if (expectExtract) {
        CheckIsFunction(extract, true);
      }
    }

    public void ResolveTypeRhs(TypeRhs rr, Statement stmt, ResolutionContext resolutionContext) {
      Contract.Requires(rr != null);
      Contract.Requires(stmt != null);
      Contract.Requires(resolutionContext != null);
      Contract.Ensures(Contract.Result<Type>() != null);

      if (rr.PreType != null) {
        // the job's already been done
        return;
      }

      if (rr is AllocateArray allocateArray) {
        // ---------- new T[EE]    OR    new T[EE] (elementInit)    OR    new T[EE] [elements...]
        var dims = allocateArray.ArrayDimensions.Count;
        resolver.ResolveType(stmt.Origin, allocateArray.ElementType, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
        int i = 0;
        foreach (var dim in allocateArray.ArrayDimensions) {
          ResolveExpression(dim, resolutionContext);
          var indexHint = dims == 1 ? "" : " for index " + i;
          AddConfirmation(PreTypeConstraints.CommonConfirmationBag.InIntFamily, dim.PreType, dim.Origin,
            $"new must use an integer-based expression for the array size (got {{0}}{indexHint})");
          i++;
        }

        var elementPreType = Type2PreType(allocateArray.ElementType);
        rr.PreType = BuiltInArrayType(dims, elementPreType);
        if (allocateArray.ElementInit != null) {
          ResolveExpression(allocateArray.ElementInit, resolutionContext);
          // Check (the pre-type version of)
          //     nat^N -> rr.EType  :>  rr.ElementInit.Type
          resolver.SystemModuleManager.CreateArrowTypeDecl(dims);  // TODO: should this be done already in the parser?
          var indexPreTypes = Enumerable.Repeat(Type2PreType(resolver.SystemModuleManager.Nat()), dims).ToList();
          var arrowPreType = BuiltInArrowType(indexPreTypes, elementPreType, true, true);
          Constraints.AddSubtypeConstraint(arrowPreType, allocateArray.ElementInit.PreType, allocateArray.ElementInit.Origin, () => {
            var hintString = !PreType.Same(arrowPreType, allocateArray.ElementInit.PreType) ? "" :
              string.Format(" (perhaps write '{0} =>' in front of the expression you gave in order to make it an arrow type)",
              dims == 1 ? "_" : "(" + Util.Comma(dims, x => "_") + ")");
            return $"array-allocation initialization expression expected to have type '{{0}}' (instead got '{{1}}'){hintString}";
          });
        } else if (allocateArray.InitDisplay != null) {
          foreach (var v in allocateArray.InitDisplay) {
            ResolveExpression(v, resolutionContext);
            AddSubtypeConstraint(elementPreType, v.PreType, v.Origin, "initial value must be assignable to array's elements (expected '{0}', got '{1}')");
          }
        }
      } else if (rr is AllocateClass allocateClass) {
        if (allocateClass.Bindings == null) {
          resolver.ResolveType(stmt.Origin, allocateClass.Path, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          if ((allocateClass.Path as UserDefinedType)?.ResolvedClass is NonNullTypeDecl cl && !(allocateClass.Path.IsTraitType && !allocateClass.Path.NormalizeExpand().IsObjectQ)) {
            // life is good
          } else {
            ReportError(rr.Origin, "new can be applied only to class types (got {0})", allocateClass.Path);
          }

          rr.Type = allocateClass.Path;
          rr.PreType = Type2PreType(allocateClass.Path);
        } else {
          string initCallName = null;
          IOrigin initCallTok = null;
          // Resolve rr.Path and do one of three things:
          // * If rr.Path denotes a type, then set EType,initCallName to rr.Path,"_ctor", which sets up a call to the anonymous constructor.
          // * If the all-but-last components of rr.Path denote a type, then do EType,initCallName := allButLast(EType),last(EType)
          // * Otherwise, report an error
          var ret = resolver.ResolveTypeLenient(rr.Origin, allocateClass.Path, resolutionContext,
            new ModuleResolver.ResolveTypeOption(ResolveTypeOptionEnum.InferTypeProxies), null, true);
          if (ret != null) {
            // The all-but-last components of rr.Path denote a type (namely, ret.ReplacementType).
            rr.PreType = Type2PreType(ret.ReplacementType);
            rr.Type = ret.ReplacementType;
            initCallName = ret.LastComponent.SuffixName;
            initCallTok = ret.LastComponent.Origin;
          } else {
            // Either rr.Path resolved correctly as a type or there was no way to drop a last component to make it into something that looked
            // like a type.  In either case, set EType,initCallName to Path,"_ctor" and continue.
            rr.PreType = Type2PreType(allocateClass.Path);
            rr.Type = allocateClass.Path;
            initCallName = "_ctor";
            initCallTok = rr.Origin;
          }

          var cl = (rr.Type as UserDefinedType).ResolvedClass as NonNullTypeDecl;
          if (cl == null || allocateClass.Type.IsTraitType) {
            ReportError(rr.Origin, "new can be applied only to class types (got {0})", rr.Type);
          } else {
            // ---------- new C.Init(EE)
            Contract.Assert(initCallName != null);
            var prevErrorCount = ErrorCount;

            // We want to create a MemberSelectExpr for the initializing method.  To do that, we create a throw-away receiver of the appropriate
            // type, create a dot-suffix expression around this receiver, and then resolve it in the usual way for dot-suffix expressions.
            // It is important that this throw-away receiver have its .PreType filled in, because the call to ResolveDotSuffix will recursive
            // down to resolve this "lhs"; that's a no-op if the .PreType is already filled in, whereas it could cause a "'this' not allowed in
            // static context" error if the code tried to resolve this "this" against the enclosing environment.
            var lhs = new ImplicitThisExprConstructorCall(initCallTok) {
              Type = allocateClass.Type,
              PreType = rr.PreType
            };
            var callLhs = new ExprDotName(((UserDefinedType)allocateClass.Type).Origin, lhs, new Name(initCallName), ret?.LastComponent.OptTypeArguments);
            ResolveDotSuffix(callLhs, false, true, allocateClass.Bindings.ArgumentBindings, resolutionContext, true);
            if (prevErrorCount == ErrorCount) {
              Contract.Assert(callLhs.ResolvedExpression is MemberSelectExpr);  // since ResolveApplySuffix succeeded and call.Lhs denotes an expression (not a module or a type)
              var methodSel = (MemberSelectExpr)callLhs.ResolvedExpression;
              if (methodSel.Member is MethodOrConstructor) {
                allocateClass.InitCall = new CallStmt(stmt.Origin, [], methodSel, allocateClass.Bindings.ArgumentBindings, initCallTok.ReportingRange);
                ResolveCallStmt(allocateClass.InitCall, resolutionContext, allocateClass.Type);
              } else {
                ReportError(initCallTok, "object initialization must denote an initializing method or constructor ({0})", initCallName);
              }
            }
          }
        }
      }
    }

    /// <summary>
    /// Checks if lhs, which is expected to be a successfully resolved expression, denotes something
    /// that can be assigned to.  In particular, this means that lhs denotes a mutable variable, field,
    /// or array element.  If a violation is detected, an error is reported.
    /// </summary>
    public void CheckIsLvalue(Expression lhs, ResolutionContext resolutionContext) {
      Contract.Requires(lhs != null);
      Contract.Requires(resolutionContext != null);
      if (lhs is IdentifierExpr) {
        var ll = (IdentifierExpr)lhs;
        if (!ll.Var.IsMutable) {
          ReportError(lhs, "LHS of assignment must denote a mutable variable");
        }
      } else if (lhs is MemberSelectExpr) {
        var ll = (MemberSelectExpr)lhs;
        var field = ll.Member as Field;
        if (field == null || !field.IsUserMutable) {
          if (resolutionContext.InFirstPhaseConstructor && field is ConstantField cf && !cf.IsStatic && cf.Rhs == null) {
            if (Expression.AsThis(ll.Obj) != null) {
              // it's cool; this field can be assigned to here
            } else {
              ReportError(lhs, "LHS of assignment must denote a mutable field of 'this'");
            }
          } else {
            ReportError(lhs, "LHS of assignment must denote a mutable field");
          }
        }
      } else if (lhs is SeqSelectExpr) {
        var ll = (SeqSelectExpr)lhs;
        var arrayType = resolver.ResolvedArrayType(ll.Seq.Origin, 1, new InferredTypeProxy(), resolutionContext, true);
        AddSubtypeConstraint(Type2PreType(arrayType), ll.Seq.PreType, ll.Seq.Origin, "LHS of array assignment must denote an array element (found {1})");
        if (!ll.SelectOne) {
          ReportError(ll, "cannot assign to a range of array elements (try the 'forall' statement)");
        }
      } else if (lhs is MultiSelectExpr) {
        // nothing to check; this can only denote an array element
      } else {
        ReportError(lhs, "LHS of assignment must denote a mutable variable or field");
      }
    }
  }
}
