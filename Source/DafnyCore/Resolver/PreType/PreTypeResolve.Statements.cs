//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System;
using System.Collections.Generic;
using System.Diagnostics.CodeAnalysis;
using System.Linq;
using System.Numerics;
using System.Diagnostics.Contracts;
using System.Runtime.Intrinsics.X86;
using JetBrains.Annotations;
using Microsoft.Boogie;
using Bpl = Microsoft.Boogie;
using ResolutionContext = Microsoft.Dafny.ResolutionContext;

namespace Microsoft.Dafny {
  public partial class PreTypeResolver {
    private Scope<Statement> enclosingStatementLabels;
    private readonly Scope<Label> dominatingStatementLabels;
    private List<Statement> loopStack = new();  // the enclosing loops (from which it is possible to break out)
    bool inBodyInitContext;  // "true" only if "currentMethod is Constructor"

    void ResolveBlockStatement(BlockStmt blockStmt, ResolutionContext resolutionContext) {
      Contract.Requires(blockStmt != null);
      Contract.Requires(resolutionContext != null);

      if (blockStmt is DividedBlockStmt div) {
        Contract.Assert(currentMethod is Constructor);  // divided bodies occur only in class constructors
        Contract.Assert(!inBodyInitContext);  // divided bodies are never nested
        inBodyInitContext = true;
        foreach (Statement ss in div.BodyInit) {
          ResolveStatementWithLabels(ss, resolutionContext);
        }
        Contract.Assert(inBodyInitContext);
        inBodyInitContext = false;
        foreach (Statement ss in div.BodyProper) {
          ResolveStatementWithLabels(ss, resolutionContext);
        }
      } else {
        foreach (Statement ss in blockStmt.Body) {
          ResolveStatementWithLabels(ss, resolutionContext);
        }
      }
    }

    void ResolveStatementWithLabels(Statement stmt, ResolutionContext resolutionContext) {
      Contract.Requires(stmt != null);
      Contract.Requires(resolutionContext != null);

      enclosingStatementLabels.PushMarker();
      // push labels
      for (var l = stmt.Labels; l != null; l = l.Next) {
        var lnode = l.Data;
        Contract.Assert(lnode.Name != null);  // LabelNode's with .Label==null are added only during resolution of the break statements with 'stmt' as their target, which hasn't happened yet
        var prev = enclosingStatementLabels.Find(lnode.Name);
        if (prev == stmt) {
          ReportError(lnode.Tok, "duplicate label");
        } else if (prev != null) {
          ReportError(lnode.Tok, "label shadows an enclosing label");
        } else {
          var r = enclosingStatementLabels.Push(lnode.Name, stmt);
          Contract.Assert(r == Scope<Statement>.PushResult.Success);  // since we just checked for duplicates, we expect the Push to succeed
          if (dominatingStatementLabels.Find(lnode.Name) != null) {
            ReportError(lnode.Tok, "label shadows a dominating label");
          } else {
            var rr = dominatingStatementLabels.Push(lnode.Name, lnode);
            Contract.Assert(rr == Scope<Label>.PushResult.Success);  // since we just checked for duplicates, we expect the Push to succeed
          }
        }
      }
      ResolveStatement(stmt, resolutionContext);
      enclosingStatementLabels.PopMarker();
    }

    public void ResolveStatement(Statement stmt, ResolutionContext resolutionContext) {
      Contract.Requires(stmt != null);
      Contract.Requires(resolutionContext != null);

      if (!(stmt is ForallStmt || stmt is ForLoopStmt)) {  // "forall" and "for" statements do their own attribute resolution below
        ResolveAttributes(stmt, resolutionContext, false);
      }
      if (stmt is PredicateStmt) {
        var s = (PredicateStmt)stmt;
        var assertStmt = stmt as AssertStmt;
        if (assertStmt != null && assertStmt.Label != null) {
          if (dominatingStatementLabels.Find(assertStmt.Label.Name) != null) {
            ReportError(assertStmt.Label.Tok, "assert label shadows a dominating label");
          } else {
            var rr = dominatingStatementLabels.Push(assertStmt.Label.Name, assertStmt.Label);
            Contract.Assert(rr == Scope<Label>.PushResult.Success);  // since we just checked for duplicates, we expect the Push to succeed
          }
        }
        ResolveExpression(s.Expr, resolutionContext);
        ConstrainTypeExprBool(s.Expr, "condition is expected to be of type bool, but is {0}");
        if (assertStmt != null && assertStmt.Proof != null) {
          // clear the labels for the duration of checking the proof body, because break statements are not allowed to leave a the proof body
          var prevLblStmts = enclosingStatementLabels;
          var prevLoopStack = loopStack;
          enclosingStatementLabels = new Scope<Statement>(resolver.Options);
          loopStack = new List<Statement>();
          ResolveStatement(assertStmt.Proof, resolutionContext);
          enclosingStatementLabels = prevLblStmts;
          loopStack = prevLoopStack;
        }
        if (stmt is ExpectStmt expectStmt) {
          if (expectStmt.Message == null) {
            expectStmt.Message = new StringLiteralExpr(s.Tok, "expectation violation", false);
          }
          ResolveExpression(expectStmt.Message, resolutionContext);
        }

      } else if (stmt is PrintStmt) {
        var s = (PrintStmt)stmt;
        var opts = resolutionContext;
        s.Args.Iter(e => ResolveExpression(e, opts));

      } else if (stmt is RevealStmt) {
        var s = (RevealStmt)stmt;
        foreach (var expr in s.Exprs) {
          var name = RevealStmt.SingleName(expr);
          var labeledAssert = name == null ? null : dominatingStatementLabels.Find(name) as AssertLabel;
          if (labeledAssert != null) {
            s.LabeledAsserts.Add(labeledAssert);
          } else {
            var revealResolutionContext = resolutionContext with { InReveal = true };
            if (expr is ApplySuffix applySuffix) {
              var methodCallInfo = ResolveApplySuffix(applySuffix, revealResolutionContext, true);
              if (methodCallInfo == null) {
                ReportError(expr.tok, "expression has no reveal lemma");
              } else if (methodCallInfo.Callee.Member is TwoStateLemma && !revealResolutionContext.IsTwoState) {
                ReportError(methodCallInfo.Tok, "a two-state function can only be revealed in a two-state context");
              } else if (methodCallInfo.Callee.AtLabel != null) {
                Contract.Assert(methodCallInfo.Callee.Member is TwoStateLemma);
                ReportError(methodCallInfo.Tok, "to reveal a two-state function, do not list any parameters or @-labels");
              } else {
                var call = new CallStmt(s.RangeToken, new List<Expression>(), methodCallInfo.Callee, methodCallInfo.ActualParameters);
                s.ResolvedStatements.Add(call);
              }
            } else {
              ResolveExpression(expr, revealResolutionContext);
            }
          }
        }
        foreach (var a in s.ResolvedStatements) {
          ResolveStatement(a, resolutionContext);
        }

      } else if (stmt is BreakStmt) {
        var s = (BreakStmt)stmt;
        if (s.TargetLabel != null) {
          Statement target = enclosingStatementLabels.Find(s.TargetLabel.val);
          if (target == null) {
            ReportError(s.TargetLabel, $"{s.Kind} label is undefined or not in scope: {s.TargetLabel.val}");
          } else if (s.IsContinue && !(target is LoopStmt)) {
            ReportError(s.TargetLabel, $"continue label must designate a loop: {s.TargetLabel.val}");
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
            Statement target = loopStack[loopStack.Count - s.BreakAndContinueCount];
            if (target.Labels == null) {
              // make sure there is a label, because the compiler and translator will want to see a unique ID
              target.Labels = new LList<Label>(new Label(target.Tok, null), null);
            }
            s.TargetStmt = target;
          }
        }

      } else if (stmt is ProduceStmt) {
        var kind = stmt is YieldStmt ? "yield" : "return";
        if (stmt is YieldStmt && !(resolutionContext.CodeContext is IteratorDecl)) {
          ReportError(stmt, "yield statement is allowed only in iterators");
        } else if (stmt is ReturnStmt && !(resolutionContext.CodeContext is Method)) {
          ReportError(stmt, "return statement is allowed only in method");
        } else if (inBodyInitContext) {
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
            List<Expression> formals = new List<Expression>();
            foreach (Formal f in cmc.Outs) {
              Expression produceLhs;
              if (stmt is ReturnStmt) {
                var ident = new IdentifierExpr(f.tok, f.Name);
                // resolve it here to avoid capture into more closely declared local variables
                Contract.Assert(f.Type != null);
                ident.Var = f;
                ident.PreType = Type2PreType(ident.Var.Type);
                produceLhs = ident;
              } else {
                var yieldIdent = new MemberSelectExpr(f.tok, new ImplicitThisExpr(f.tok), f.Name);
                ResolveExpression(yieldIdent, resolutionContext);
                produceLhs = yieldIdent;
              }
              formals.Add(produceLhs);
            }
            s.HiddenUpdate = new UpdateStmt(s.RangeToken, formals, s.Rhss, true);
            // resolving the update statement will check for return/yield statement specifics.
            ResolveStatement(s.HiddenUpdate, resolutionContext);
          }
        }

      } else if (stmt is ConcreteUpdateStatement concreteUpdateStatement) {
        ResolveConcreteUpdateStmt(concreteUpdateStatement, null, resolutionContext);

      } else if (stmt is VarDeclStmt varDeclStmt) {
        ResolveConcreteUpdateStmt(varDeclStmt.Update, varDeclStmt.Locals, resolutionContext);

      } else if (stmt is VarDeclPattern) {
        var s = (VarDeclPattern)stmt;
        foreach (var local in s.LocalVars) {
          int prevErrorCount = ErrorCount;
          resolver.ResolveType(local.Tok, local.OptionalType, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          local.type = ErrorCount == prevErrorCount ? local.type = local.OptionalType : new InferredTypeProxy();
          local.PreType = Type2PreType(local.type);
        }
        ResolveExpression(s.RHS, resolutionContext);
        ResolveCasePattern(s.LHS, s.RHS.PreType, resolutionContext);
        // Check for duplicate names now, because not until after resolving the case pattern do we know if identifiers inside it refer to bound variables or nullary constructors
        var c = 0;
        foreach (var bv in s.LHS.Vars) {
          ScopePushAndReport(scope, bv.Name, bv, bv.Tok, "local variable");
          c++;
        }
        if (c == 0) {
          // Every identifier-looking thing in the pattern resolved to a constructor; that is, this LHS is a constant literal
          ReportError(s.LHS.tok, "LHS is a constant literal; to be legal, it must introduce at least one bound variable");
        }

      } else if (stmt is AssignStmt) {
        var s = (AssignStmt)stmt;
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
          AddSubtypeConstraint(lhsPreType, rr.Expr.PreType, stmt.Tok, "RHS (of type {1}) not assignable to LHS (of type {0})");
        } else if (s.Rhs is TypeRhs) {
          var rr = (TypeRhs)s.Rhs;
          ResolveTypeRhs(rr, stmt, resolutionContext);
          AddSubtypeConstraint(lhsPreType, rr.PreType, stmt.Tok, "type {1} is not assignable to LHS (of type {0})");
        } else if (s.Rhs is HavocRhs) {
          // nothing else to do
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected RHS
        }

      } else if (stmt is CallStmt callStmt) {
        ResolveCallStmt(callStmt, resolutionContext, null);

      } else if (stmt is BlockStmt blockStmt) {
        scope.PushMarker();
        ResolveBlockStatement(blockStmt, resolutionContext);
        scope.PopMarker();

      } else if (stmt is IfStmt) {
        var s = (IfStmt)stmt;
        if (s.Guard != null) {
          ResolveExpression(s.Guard, resolutionContext);
          ConstrainTypeExprBool(s.Guard, "if statement", "condition is expected to be of type bool, but is {0}");
        }

        scope.PushMarker();
        if (s.IsBindingGuard) {
          var exists = (ExistsExpr)s.Guard;
          foreach (var v in exists.BoundVars) {
            ScopePushAndReport(v, "bound-variable", false);
          }
        }
        dominatingStatementLabels.PushMarker();
        ResolveBlockStatement(s.Thn, resolutionContext);
        dominatingStatementLabels.PopMarker();
        scope.PopMarker();

        if (s.Els != null) {
          dominatingStatementLabels.PushMarker();
          ResolveStatement(s.Els, resolutionContext);
          dominatingStatementLabels.PopMarker();
        }

      } else if (stmt is AlternativeStmt) {
        var s = (AlternativeStmt)stmt;
        ResolveAlternatives(s.Alternatives, null, resolutionContext);

      } else if (stmt is OneBodyLoopStmt oneBodyLoopStmt) {
        ResolveOneBodyLoopStmt(oneBodyLoopStmt, resolutionContext);

      } else if (stmt is AlternativeLoopStmt) {
        var s = (AlternativeLoopStmt)stmt;
        ResolveAlternatives(s.Alternatives, s, resolutionContext);
        ResolveLoopSpecificationComponents(s.Invariants, s.Decreases, s.Mod, resolutionContext);

      } else if (stmt is ForallStmt) {
        var s = (ForallStmt)stmt;

        int prevErrorCount = ErrorCount;
        scope.PushMarker();
        foreach (BoundVar v in s.BoundVars) {
          resolver.ResolveType(v.tok, v.Type, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
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
          var prevLblStmts = enclosingStatementLabels;
          var prevLoopStack = loopStack;
          enclosingStatementLabels = new Scope<Statement>(resolver.Options);
          loopStack = new List<Statement>();
          ResolveStatement(s.Body, resolutionContext);
          enclosingStatementLabels = prevLblStmts;
          loopStack = prevLoopStack;
        } else {
          ReportWarning(s.Tok, "note, this forall statement has no body");
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
            if (s0 is AssignStmt) {
              s.Kind = ForallStmt.BodyKind.Assign;

              var rhs = ((AssignStmt)s0).Rhs;
              if (rhs is TypeRhs) {
                ReportError(rhs.Tok, "new allocation not supported in aggregate assignments");
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
              ReportInfo(s.Tok, "ensures " + Printer.ExprToString(resolver.Options, result));
            } else {
              s.Kind = ForallStmt.BodyKind.Proof;
              if (s.Body is BlockStmt && ((BlockStmt)s.Body).Body.Count == 0) {
                // an empty statement, so don't produce any warning
              } else {
                ReportWarning(s.Tok, "the conclusion of the body of this forall statement will not be known outside the forall statement; consider using an 'ensures' clause");
              }
            }
          }

          if (s.ForallExpressions != null) {
            foreach (Expression expr in s.ForallExpressions) {
              ResolveExpression(expr, resolutionContext);
            }
          }
        }

      } else if (stmt is ModifyStmt modifyStmt) {
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
        ReportError(stmt.Tok, "skeleton statements are allowed only in refining methods");
        // nevertheless, resolve the underlying statement; hey, why not
        if (skeletonStatement.S != null) {
          ResolveStatement(skeletonStatement.S, resolutionContext);
        }

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();
      }
    }

    private void ResolveOneBodyLoopStmt(OneBodyLoopStmt s, ResolutionContext resolutionContext) {
      Contract.Requires(s != null);
      Contract.Requires(resolutionContext != null);

      if (s is WhileStmt whileS && whileS.Guard != null) {
        ResolveExpression(whileS.Guard, resolutionContext);
        ConstrainTypeExprBool(whileS.Guard, "condition is expected to be of type bool, but is {0}");

      } else if (s is ForLoopStmt forS) {
        var loopIndex = forS.LoopIndex;
        resolver.ResolveType(loopIndex.tok, loopIndex.Type, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
        loopIndex.PreType = Type2PreType(loopIndex.Type);
        AddConfirmation("InIntFamily", loopIndex.PreType, loopIndex.tok, "index variable is expected to be of an integer type (got {0})");

        ResolveExpression(forS.Start, resolutionContext);
        AddSubtypeConstraint(loopIndex.PreType, forS.Start.PreType, forS.Start.tok,
          "lower bound (of type {1}) not assignable to index variable (of type {0})");
        if (forS.End != null) {
          ResolveExpression(forS.End, resolutionContext);
          AddSubtypeConstraint(loopIndex.PreType, forS.End.PreType, forS.End.tok,
            "upper bound (of type {1}) not assignable to index variable (of type {0})");
          if (forS.Decreases.Expressions.Count != 0) {
            ReportError(forS.Decreases.Expressions[0].tok,
              "a 'for' loop is allowed an explicit 'decreases' clause only if the end-expression is '*'");
          }
        } else if (forS.Decreases.Expressions.Count == 0 && !resolutionContext.CodeContext.AllowsNontermination) {
          // note, the following error message is also emitted elsewhere (if the loop bears a "decreases *")
          ReportError(forS.Tok,
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
        dominatingStatementLabels.PushMarker();
        ResolveStatement(s.Body, resolutionContext);
        dominatingStatementLabels.PopMarker();
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
        // Usually, we'd use == as the default main operator.  However, if the calculation
        // begins or ends with a boolean literal, then we can do better by selecting ==>
        // or <==.  Also, if the calculation begins or ends with an empty set, then we can
        // do better by selecting <= or >=.
        if (s.Lines.Count == 0) {
          s.Op = CalcStmt.DefaultOp;
        } else {
          bool b;
          if (Expression.IsBoolLiteral(s.Lines.First(), out b)) {
            s.Op = new CalcStmt.BinaryCalcOp(b ? BinaryExpr.Opcode.Imp : BinaryExpr.Opcode.Exp);
          } else if (Expression.IsBoolLiteral(s.Lines.Last(), out b)) {
            s.Op = new CalcStmt.BinaryCalcOp(b ? BinaryExpr.Opcode.Exp : BinaryExpr.Opcode.Imp);
          } else if (Expression.IsEmptySetOrMultiset(s.Lines.First())) {
            s.Op = new CalcStmt.BinaryCalcOp(BinaryExpr.Opcode.Ge);
          } else if (Expression.IsEmptySetOrMultiset(s.Lines.Last())) {
            s.Op = new CalcStmt.BinaryCalcOp(BinaryExpr.Opcode.Le);
          } else {
            s.Op = CalcStmt.DefaultOp;
          }
        }
        ReportInfo(s.Tok, s.Op.ToString());
      }

      if (s.Lines.Count > 0) {
        PreType linePreType = CreatePreTypeProxy("calc line");
        var e0 = s.Lines.First();
        ResolveExpression(e0, resolutionContext);
        AddSubtypeConstraint(linePreType, e0.PreType, e0.tok, "all lines in a calculation must have the same type (got {1} after {0})");
        for (var i = 1; i < s.Lines.Count; i++) {
          var e1 = s.Lines[i];
          ResolveExpression(e1, resolutionContext);
#if SOON
          // reuse the error object if we're on the dummy line; this prevents a duplicate error message
#endif
          AddSubtypeConstraint(linePreType, e1.PreType, e1.tok, "all lines in a calculation must have the same type (got {1} after {0})");
          var step = (s.StepOps[i - 1] ?? s.Op).StepExpr(e0, e1); // Use custom line operator
          ResolveExpression(step, resolutionContext);
          s.Steps.Add(step);
          e0 = e1;
        }

        // clear the labels for the duration of checking the hints, because break statements are not allowed to leave a forall statement
        var prevLblStmts = enclosingStatementLabels;
        var prevLoopStack = loopStack;
        enclosingStatementLabels = new Scope<Statement>(resolver.Options);
        loopStack = new List<Statement>();
        foreach (var h in s.Hints) {
          foreach (var oneHint in h.Body) {
            dominatingStatementLabels.PushMarker();
            ResolveStatement(oneHint, resolutionContext);
            dominatingStatementLabels.PopMarker();
          }
        }
        enclosingStatementLabels = prevLblStmts;
        loopStack = prevLoopStack;
      }
      if (prevErrorCount == ErrorCount && s.Lines.Count > 0) {
        // do not build Result from the lines if there were errors, as it might be ill-typed and produce unnecessary resolution errors
        var resultOp = s.StepOps.Aggregate(s.Op, (op0, op1) => op1 == null ? op0 : op0.ResultOp(op1));
        s.Result = resultOp.StepExpr(s.Lines.First(), s.Lines.Last());
      } else {
        s.Result = CalcStmt.DefaultOp.StepExpr(Expression.CreateIntLiteral(s.Tok, 0), Expression.CreateIntLiteral(s.Tok, 0));
      }
      ResolveExpression(s.Result, resolutionContext);
      Contract.Assert(s.Result != null);
      Contract.Assert(prevErrorCount != ErrorCount || s.Steps.Count == s.Hints.Count);
    }

    private void ResolveConcreteUpdateStmt(ConcreteUpdateStatement update, List<LocalVariable> locals, ResolutionContext resolutionContext) {
      Contract.Requires(update != null || locals != null);
      // We have four cases.
      Contract.Assert(update == null || update is AssignSuchThatStmt || update is UpdateStmt || update is AssignOrReturnStmt);
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
      if (update is UpdateStmt updateStatement) {
        foreach (var rhs in updateStatement.Rhss) {
          ResolveAssignmentRhs(rhs, updateStatement, resolutionContext);
        }
      } else if (update is AssignOrReturnStmt elephantStmt) {
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
          resolver.ResolveType(local.Tok, local.OptionalType, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          local.type = ErrorCount == prevErrorCount ? local.OptionalType : new InferredTypeProxy();
          ScopePushAndReport(local, "local-variable", true);
        }
        // With the new locals in scope, it's now time to resolve the attributes on all the locals
        foreach (var local in locals) {
          ResolveAttributes(local, resolutionContext, false);
        }
      }

      // Resolve the LHSs
      if (update != null) {
        foreach (var lhs in update.Lhss) {
          ResolveExpression(lhs, resolutionContext);
        }
      }

      if (update is AssignSuchThatStmt assignSuchThatStmt) {
        ResolveAssignSuchThatStmt(assignSuchThatStmt, resolutionContext);
      } else if (update is UpdateStmt updateStmt) {
        ResolveUpdateStmt(updateStmt, resolutionContext, errorCountBeforeCheckingStmt);
      } else if (update is AssignOrReturnStmt assignOrReturnStmt) {
        ResolveAssignOrReturnStmt(assignOrReturnStmt, resolutionContext);
      } else {
        Contract.Assert(update == null);
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
    }

    /// <summary>
    /// Assumes that LHSs and RHSs have already been resolved.
    /// Resolve the entire UpdateStmt.
    /// errorCountBeforeCheckingStmt is passed in so that this method can determine if any resolution errors were found during
    /// LHS or RHS checking, because only if no errors were found is update.ResolvedStmt changed.
    /// </summary>
    private void ResolveUpdateStmt(UpdateStmt update, ResolutionContext resolutionContext, int errorCountBeforeCheckingStmt) {
      Contract.Requires(update != null);
      Contract.Requires(resolutionContext != null);
      IToken firstEffectfulRhs = null;
      MethodCallInformation methodCallInfo = null;
      update.ResolvedStatements = new();
      foreach (var rhs in update.Rhss) {
        bool isEffectful;
        if (rhs is TypeRhs tr) {
          isEffectful = tr.InitCall != null;
        } else if (rhs is HavocRhs) {
          isEffectful = false;
        } else {
          var er = (ExprRhs)rhs;
          if (er.Expr is ApplySuffix applySuffix) {
            var cRhs = ResolveApplySuffix(applySuffix, resolutionContext, true); // TODO: don't re-resolve the RHS, only obtain the cRhs return value
            isEffectful = cRhs != null;
            methodCallInfo = methodCallInfo ?? cRhs;
          } else {
            isEffectful = false;
          }
        }
        if (isEffectful && firstEffectfulRhs == null) {
          firstEffectfulRhs = rhs.Tok;
        }

        ResolveAttributes(rhs, resolutionContext, false);
      }

      // figure out what kind of UpdateStmt this is
      if (firstEffectfulRhs == null) {
        if (update.Lhss.Count == 0) {
          Contract.Assert(update.Rhss.Count == 1);  // guaranteed by the parser
          ReportError(update, "expected method call, found expression");
        } else if (update.Lhss.Count != update.Rhss.Count) {
          ReportError(update, "the number of left-hand sides ({0}) and right-hand sides ({1}) must match for a multi-assignment",
            update.Lhss.Count, update.Rhss.Count);
        } else if (ErrorCount == errorCountBeforeCheckingStmt) {
          // add the statements here in a sequence, but don't use that sequence later for translation (instead, should translate properly as multi-assignment)
          for (var i = 0; i < update.Lhss.Count; i++) {
            var a = new AssignStmt(update.RangeToken, update.Lhss[i].Resolved, update.Rhss[i]);
            update.ResolvedStatements.Add(a);
          }
        }

      } else if (update.CanMutateKnownState) {
        if (1 < update.Rhss.Count) {
          ReportError(firstEffectfulRhs, "cannot have effectful parameter in multi-return statement.");
        } else { // it might be ok, if it is a TypeRhs
          Contract.Assert(update.Rhss.Count == 1);
          if (methodCallInfo != null) {
            ReportError(methodCallInfo.Tok, "cannot have method call in return statement.");
          } else {
            // we have a TypeRhs
            var tr = (TypeRhs)update.Rhss[0];
            Contract.Assert(tr.InitCall != null); // there were effects, so this must have been a call.
            if (tr.CanAffectPreviouslyKnownExpressions) {
              ReportError(tr.Tok, "can only have initialization methods which modify at most 'this'.");
            } else if (ErrorCount == errorCountBeforeCheckingStmt) {
              var a = new AssignStmt(update.RangeToken, update.Lhss[0].Resolved, tr);
              update.ResolvedStatements.Add(a);
            }
          }
        }

      } else {
        // if there was an effectful RHS, that must be the only RHS
        if (update.Rhss.Count != 1) {
          ReportError(firstEffectfulRhs, "an update statement is allowed an effectful RHS only if there is just one RHS");
        } else if (methodCallInfo == null) {
          // must be a single TypeRhs
          if (update.Lhss.Count != 1) {
            Contract.Assert(2 <= update.Lhss.Count);  // the parser allows 0 Lhss only if the whole statement looks like an expression (not a TypeRhs)
            ReportError(update.Lhss[1].tok, "the number of left-hand sides ({0}) and right-hand sides ({1}) must match for a multi-assignment",
              update.Lhss.Count, update.Rhss.Count);
          } else if (ErrorCount == errorCountBeforeCheckingStmt) {
            var a = new AssignStmt(update.RangeToken, update.Lhss[0].Resolved, update.Rhss[0]);
            update.ResolvedStatements.Add(a);
          }
        } else if (ErrorCount == errorCountBeforeCheckingStmt) {
          // a call statement
          var resolvedLhss = update.Lhss.ConvertAll(ll => ll.Resolved);
          var a = new CallStmt(update.RangeToken, resolvedLhss, methodCallInfo.Callee, methodCallInfo.ActualParameters);
          a.OriginalInitialLhs = update.OriginalInitialLhs;
          update.ResolvedStatements.Add(a);
        }
      }

      foreach (var a in update.ResolvedStatements) {
        ResolveStatement(a, resolutionContext);
      }
    }

    /// <summary>
    /// Resolve an assign-such-that statement. It is assumed that the LHSs have already been resolved,
    /// but not the RHSs.
    /// </summary>
    private void ResolveAssignSuchThatStmt(AssignSuchThatStmt s, ResolutionContext resolutionContext) {
      Contract.Requires(s != null);
      Contract.Requires(resolutionContext != null);

      var lhsSimpleVariables = new HashSet<IVariable>();
      foreach (var lhs in s.Lhss) {
        CheckIsLvalue(lhs.Resolved, resolutionContext);
        if (lhs.Resolved is IdentifierExpr ide) {
          if (lhsSimpleVariables.Contains(ide.Var)) {
            // syntactically forbid duplicate simple-variables on the LHS
            ReportError(lhs, $"variable '{ide.Var.Name}' occurs more than once as left-hand side of :|");
          } else {
            lhsSimpleVariables.Add(ide.Var);
          }
        }
        // to ease in the verification of the existence check, only allow local variables as LHSs
        if (s.AssumeToken == null && !(lhs.Resolved is IdentifierExpr)) {
          ReportError(lhs, "an assign-such-that statement (without an 'assume' clause) currently supports only local-variable LHSs");
        }
      }

      ResolveExpression(s.Expr, resolutionContext);
      ConstrainTypeExprBool(s.Expr, "type of RHS of assign-such-that statement must be boolean (got {0})");
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
            ReportError(s.Tok, "a method called as an initialization method must not be 'static'");
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
        // resolve arguments
        ResolveActualParameters(s.Bindings, callee.Ins, s.Tok, callee, resolutionContext, typeMap,
          callee.IsStatic ? null : s.Receiver);
        // type check the out-parameter arguments (in-parameters were type checked as part of ResolveActualParameters)
        for (var i = 0; i < callee.Outs.Count && i < s.Lhs.Count; i++) {
          var outFormal = callee.Outs[i];
          var st = outFormal.PreType.Substitute(typeMap);
          var lhs = s.Lhs[i];
          var what = GetLocationInformation(outFormal, callee.Outs.Count, i, "method out-parameter");

          AddSubtypeConstraint(lhs.PreType, st, s.Tok, $"incorrect return type {what} (expected {{1}}, got {{0}})");
        }
        for (int i = 0; i < s.Lhs.Count; i++) {
          var lhs = s.Lhs[i];
          // LHS must denote a mutable field.
          CheckIsLvalue(lhs.Resolved, resolutionContext);
        }

#if SOON
        // Resolution termination check
        ModuleDefinition callerModule = resolutionContext.EnclosingModule;
        ModuleDefinition calleeModule = ((ICodeContext)callee).EnclosingModule;
        if (callerModule == calleeModule) {
          // intra-module call; add edge in module's call graph
          var caller = CodeContextWrapper.Unwrap(resolutionContext) as ICallable;
          if (caller == null) {
            // don't add anything to the call graph after all
          } else if (caller is IteratorDecl) {
            callerModule.CallGraph.AddEdge(((IteratorDecl)caller).Member_MoveNext, callee);
          } else {
            callerModule.CallGraph.AddEdge(caller, callee);
            if (caller == callee) {
              callee.IsRecursive = true;  // self recursion (mutual recursion is determined elsewhere)
            }
          }
        }
#endif
      }
      if (Contract.Exists(callee.Decreases.Expressions, e => e is WildcardExpr) && !resolutionContext.CodeContext.AllowsNontermination) {
        ReportError(s.Tok, "a call to a possibly non-terminating method is allowed only if the calling method is also declared (with 'decreases *') to be possibly non-terminating");
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
      Method callee = null;
      Contract.Assert(s.Rhss != null);
      if (s.Rhss.Count == 0 && s.Rhs.Expr is ApplySuffix asx) {
        var methodCallInfo = ResolveApplySuffix(asx, resolutionContext, true);
        callee = methodCallInfo?.Callee.Member as Method;
        if (callee != null) {
          // We're looking at a method call
          if (callee.Outs.Count != 0) {
            var typeMap = PreType.PreTypeSubstMap(callee.TypeArgs, methodCallInfo.Callee.PreTypeApplication_JustMember);
            firstPreType = callee.Outs[0].PreType.Substitute(typeMap);
          } else {
            ReportError(s.Rhs.tok, $"Expected '{callee.Name}' to have a success/failure output value, but the method returns nothing.");
          }
        } else {
          // We're looking at a call to a function. Treat it like any other expression.
          firstPreType = asx.PreType;
        }
      } else {
        ResolveExpression(s.Rhs.Expr, resolutionContext);
        firstPreType = s.Rhs.Expr.PreType;
      }

      var enclosingMethod = (Method)resolutionContext.CodeContext;
      if (enclosingMethod.Outs.Count == 0 && s.KeywordToken == null) {
        ReportError(s.Tok, $"A method containing a :- statement must have an out-parameter ({enclosingMethod.Name})");
        return;
      }
      TopLevelDeclWithMembers failureSupportingType = null;
      if (firstPreType != null) {
        PartiallySolveTypeConstraints();
        failureSupportingType = (firstPreType.Normalize() as DPreType)?.Decl as TopLevelDeclWithMembers;
        if (failureSupportingType != null) {
          if (failureSupportingType.Members.Find(x => x.Name == "IsFailure") == null) {
            ReportError(s.Tok, $"member IsFailure does not exist in {firstPreType}, in :- statement");
            return;
          }
          expectExtract = failureSupportingType.Members.Find(x => x.Name == "Extract") != null;
          if (expectExtract && callee == null && s.Lhss.Count != 1 + s.Rhss.Count) {
            ReportError(s.Tok,
              "number of lhs ({0}) must match number of rhs ({1}) for a rhs type ({2}) with member Extract",
              s.Lhss.Count, 1 + s.Rhss.Count, firstPreType);
            return;
          } else if (expectExtract && callee != null && s.Lhss.Count != callee.Outs.Count) {
            ReportError(s.Tok,
              "wrong number of method result arguments (got {0}, expected {1}) for a rhs type ({2}) with member Extract",
              s.Lhss.Count, callee.Outs.Count, firstPreType);
            return;
          } else if (!expectExtract && callee == null && s.Lhss.Count != s.Rhss.Count) {
            ReportError(s.Tok, "number of lhs ({0}) must be one less than number of rhs ({1}) for a rhs type ({2}) without member Extract",
              s.Lhss.Count, 1 + s.Rhss.Count, firstPreType);
            return;
          } else if (!expectExtract && callee != null && s.Lhss.Count != callee.Outs.Count - 1) {
            ReportError(s.Tok, "wrong number of method result arguments (got {0}, expected {1}) for a rhs type ({2}) without member Extract",
              s.Lhss.Count, callee.Outs.Count - 1, firstPreType);
            return;
          }
        } else {
          ReportError(s.Tok,
            $"The type of the first expression to the right of ':-' could not be determined to be a failure type (got '{firstPreType}')");
          return;
        }
      } else {
        ReportError(s.Tok, "Internal Error: Unknown failure type in :- statement");
        return;
      }

      Expression lhsExtract = null;
      if (expectExtract) {
        if (enclosingMethod.Outs.Count == 0 && s.KeywordToken == null) {
          ReportError(s.Rhs.tok, $"Expected {enclosingMethod.Name} to have a Success/Failure output value");
          return;
        }

        lhsExtract = s.Lhss[0];
        var lhsResolved = lhsExtract.Resolved;
        // Make a new unresolved expression
        if (lhsResolved is MemberSelectExpr lexr) {
          Expression id = Expression.AsThis(lexr.Obj) != null ? lexr.Obj : resolver.makeTemp("recv", s, resolutionContext, lexr.Obj);
          var lex = lhsExtract as ExprDotName; // might be just a NameSegment
          lhsExtract = new ExprDotName(lexr.tok, id, lexr.MemberName, lex?.OptTypeArguments);
        } else if (lhsResolved is SeqSelectExpr lseq) {
          if (!lseq.SelectOne || lseq.E0 == null) {
            ReportError(s.Tok, "Element ranges not allowed as l-values");
            return;
          }
          Expression id = resolver.makeTemp("recv", s, resolutionContext, lseq.Seq);
          Expression id0 = id0 = resolver.makeTemp("idx", s, resolutionContext, lseq.E0);
          lhsExtract = new SeqSelectExpr(lseq.tok, lseq.SelectOne, id, id0, null, lseq.CloseParen);
          lhsExtract.Type = lseq.Type;
        } else if (lhsResolved is MultiSelectExpr lmulti) {
          Expression id = resolver.makeTemp("recv", s, resolutionContext, lmulti.Array);
          var idxs = new List<Expression>();
          foreach (var i in lmulti.Indices) {
            Expression idx = resolver.makeTemp("idx", s, resolutionContext, i);
            idxs.Add(idx);
          }
          lhsExtract = new MultiSelectExpr(lmulti.tok, id, idxs);
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
      var lhss = new List<LocalVariable>() { new LocalVariable(s.RangeToken, temp, new InferredTypeProxy(), false) };
      // "var temp ;"
      s.ResolvedStatements.Add(new VarDeclStmt(s.RangeToken, lhss, null));
      var lhss2 = new List<Expression>() { new IdentifierExpr(s.Tok, temp) };
      for (int k = (expectExtract ? 1 : 0); k < s.Lhss.Count; ++k) {
        lhss2.Add(s.Lhss[k]);
      }
      List<AssignmentRhs> rhss2 = new List<AssignmentRhs>() { s.Rhs };
      rhss2.AddRange(s.Rhss);
      if (s.Rhss.Count > 0) {
        if (lhss2.Count != rhss2.Count) {
          ReportError(s.Tok, "Mismatch in expected number of LHSs and RHSs");
          if (lhss2.Count < rhss2.Count) {
            rhss2.RemoveRange(lhss2.Count, rhss2.Count - lhss2.Count);
          } else {
            lhss2.RemoveRange(rhss2.Count, lhss2.Count - rhss2.Count);
          }
        }
      }
      // " temp, ... := MethodOrExpression, ...;"
      UpdateStmt up = new UpdateStmt(s.RangeToken, lhss2, rhss2);
      if (expectExtract) {
        up.OriginalInitialLhs = s.Lhss.Count == 0 ? null : s.Lhss[0];
      }
      s.ResolvedStatements.Add(up);

      if (s.KeywordToken != null) {
        var notFailureExpr = new UnaryOpExpr(s.Tok, UnaryOpExpr.Opcode.Not, resolver.VarDotMethod(s.Tok, temp, "IsFailure"));
        Statement ss = null;
        if (s.KeywordToken.Token.val == "expect") {
          // "expect !temp.IsFailure(), temp"
          ss = new ExpectStmt(new RangeToken(s.Tok, s.EndToken), notFailureExpr, new IdentifierExpr(s.Tok, temp), s.KeywordToken.Attrs);
        } else if (s.KeywordToken.Token.val == "assume") {
          ss = new AssumeStmt(new RangeToken(s.Tok, s.EndToken), notFailureExpr, s.KeywordToken.Attrs);
        } else if (s.KeywordToken.Token.val == "assert") {
          ss = new AssertStmt(new RangeToken(s.Tok, s.EndToken), notFailureExpr, null, null, s.KeywordToken.Attrs);
        } else {
          Contract.Assert(false, $"Invalid token in :- statement: {s.KeywordToken.Token.val}");
        }
        s.ResolvedStatements.Add(ss);
      } else {
        var enclosingOutParameter = ((Method)resolutionContext.CodeContext).Outs[0];
        var ident = new IdentifierExpr(s.Tok, enclosingOutParameter.Name) {
          // resolve it here to avoid capture into more closely declared local variables
          Var = enclosingOutParameter,
          Type = enclosingOutParameter.Type,
          PreType = enclosingOutParameter.PreType
        };

        s.ResolvedStatements.Add(
          // "if temp.IsFailure()"
          new IfStmt(s.RangeToken, false, resolver.VarDotMethod(s.Tok, temp, "IsFailure"),
            // THEN: { out := temp.PropagateFailure(); return; }
            new BlockStmt(s.RangeToken, new List<Statement>() {
              new UpdateStmt(s.RangeToken,
                new List<Expression>() { ident },
                new List<AssignmentRhs>() {new ExprRhs(resolver.VarDotMethod(s.Tok, temp, "PropagateFailure"))}
              ),
              new ReturnStmt(s.RangeToken, null),
            }),
            // ELSE: no else block
            null
          ));
      }

      if (expectExtract) {
        // "y := temp.Extract();"
        var lhs = s.Lhss[0];
        s.ResolvedStatements.Add(
          new UpdateStmt(s.RangeToken,
            new List<Expression>() { lhsExtract },
            new List<AssignmentRhs>() { new ExprRhs(resolver.VarDotMethod(s.Tok, temp, "Extract")) }
          ));
      }

      s.ResolvedStatements.ForEach(a => ResolveStatement(a, resolutionContext));
      EnsureSupportsErrorHandling(s.Tok, failureSupportingType, expectExtract, s.KeywordToken != null);
    }

    private void EnsureSupportsErrorHandling(IToken tok, TopLevelDeclWithMembers failureSupportingType, bool expectExtract, bool hasKeywordToken) {

      var isFailure = failureSupportingType.Members.Find(x => x.Name == "IsFailure");
      var propagateFailure = failureSupportingType.Members.Find(x => x.Name == "PropagateFailure");
      var extract = failureSupportingType.Members.Find(x => x.Name == "Extract");

      if (hasKeywordToken) {
        if (isFailure == null || (extract != null) != expectExtract) {
          // more details regarding which methods are missing have already been reported by regular resolution
          ReportError(tok,
            "The right-hand side of ':-', which is of type '{0}', with a keyword token must have function{1}", failureSupportingType,
            expectExtract ? "s 'IsFailure()' and 'Extract()'" : " 'IsFailure()', but not 'Extract()'");
        }
      } else {
        if (isFailure == null || propagateFailure == null || (extract != null) != expectExtract) {
          // more details regarding which methods are missing have already been reported by regular resolution
          ReportError(tok,
            "The right-hand side of ':-', which is of type '{0}', must have function{1}", failureSupportingType,
            expectExtract
              ? "s 'IsFailure()', 'PropagateFailure()', and 'Extract()'"
              : "s 'IsFailure()' and 'PropagateFailure()', but not 'Extract()'");
        }
      }

      void checkIsFunction([CanBeNull] MemberDecl memberDecl, bool allowMethod) {
        if (memberDecl == null || memberDecl is Function) {
          // fine
        } else if (allowMethod && memberDecl is Method) {
          // give a deprecation warning, so we will remove this language feature around the Dafny 4 time frame
          resolver.reporter.Deprecated(MessageSource.Resolver, ErrorRegistry.NoneId, tok,
            $"Support for member '{memberDecl.Name}' in type '{failureSupportingType}' (used indirectly via a :- statement) being a method is deprecated;" +
            " declare it to be a function instead");
        } else {
          // not allowed
          resolver.reporter.Error(MessageSource.Resolver, tok,
            $"Member '{memberDecl.Name}' in type '{failureSupportingType}' (used indirectly via a :- statement) is expected to be a function");
        }
      }

      checkIsFunction(isFailure, false);
      if (!hasKeywordToken) {
        checkIsFunction(propagateFailure, true);
      }
      if (expectExtract) {
        checkIsFunction(extract, true);
      }
    }

    void ResolveTypeRhs(TypeRhs rr, Statement stmt, ResolutionContext resolutionContext) {
      Contract.Requires(rr != null);
      Contract.Requires(stmt != null);
      Contract.Requires(resolutionContext != null);
      Contract.Ensures(Contract.Result<Type>() != null);

      if (rr.PreType != null) {
        // the job's already been done
        return;
      }

      if (rr.ArrayDimensions != null) {
        // ---------- new T[EE]    OR    new T[EE] (elementInit)
        var dims = rr.ArrayDimensions.Count;
        Contract.Assert(rr.Bindings == null && rr.Path == null && rr.InitCall == null);
        resolver.ResolveType(stmt.Tok, rr.EType, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
        int i = 0;
        foreach (var dim in rr.ArrayDimensions) {
          ResolveExpression(dim, resolutionContext);
          var indexHint = dims == 1 ? "" : " for index " + i;
          AddConfirmation("InIntFamily", dim.PreType, dim.tok,
            $"new must use an integer-based expression for the array size (got {{0}}{indexHint})");
          i++;
        }
        rr.PreType = BuiltInArrayType(dims, Type2PreType(rr.EType));
        if (rr.ElementInit != null) {
          ResolveExpression(rr.ElementInit, resolutionContext);
          // Check (the pre-type version of)
          //     nat^N -> rr.EType  :>  rr.ElementInit.Type
          resolver.builtIns.CreateArrowTypeDecl(dims);  // TODO: should this be done already in the parser?
          var indexPreTypes = Enumerable.Repeat(Type2PreType(resolver.builtIns.Nat()), dims).ToList();
          var arrowPreType = BuiltInArrowType(indexPreTypes, Type2PreType(rr.EType));
          AddSubtypeConstraint(arrowPreType, rr.ElementInit.PreType, rr.ElementInit.tok, () => {
            var hintString = !PreType.Same(arrowPreType, rr.ElementInit.PreType) ? "" :
              string.Format(" (perhaps write '{0} =>' in front of the expression you gave in order to make it an arrow type)",
              dims == 1 ? "_" : "(" + Util.Comma(dims, x => "_") + ")");
            return $"array-allocation initialization expression expected to have type '{{0}}' (instead got '{{1}}'){hintString}";
          });
        } else if (rr.InitDisplay != null) {
          foreach (var v in rr.InitDisplay) {
            ResolveExpression(v, resolutionContext);
            AddSubtypeConstraint(Type2PreType(rr.EType), v.PreType, v.tok, "initial value must be assignable to array's elements (expected '{0}', got '{1}')");
          }
        }
      } else {
        bool callsConstructor = false;
        if (rr.Bindings == null) {
          resolver.ResolveType(stmt.Tok, rr.EType, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          var cl = (rr.EType as UserDefinedType)?.ResolvedClass as NonNullTypeDecl;
          if (cl != null && !(rr.EType.IsTraitType && !rr.EType.NormalizeExpand().IsObjectQ)) {
            // life is good
          } else {
            ReportError(stmt, "new can be applied only to class types (got {0})", rr.EType);
          }
        } else {
            string initCallName = null;
            IToken initCallTok = null;
            // Resolve rr.Path and do one of three things:
            // * If rr.Path denotes a type, then set EType,initCallName to rr.Path,"_ctor", which sets up a call to the anonymous constructor.
            // * If the all-but-last components of rr.Path denote a type, then do EType,initCallName := allButLast(EType),last(EType)
            // * Otherwise, report an error
            var ret = resolver.ResolveTypeLenient(rr.Tok, rr.Path, resolutionContext,
              new Resolver.ResolveTypeOption(ResolveTypeOptionEnum.InferTypeProxies), null, true);
            if (ret != null) {
              // The all-but-last components of rr.Path denote a type (namely, ret.ReplacementType).
              rr.EType = ret.ReplacementType;
              initCallName = ret.LastComponent.SuffixName;
              initCallTok = ret.LastComponent.tok;
            } else {
              // Either rr.Path resolved correctly as a type or there was no way to drop a last component to make it into something that looked
              // like a type.  In either case, set EType,initCallName to Path,"_ctor" and continue.
              rr.EType = rr.Path;
              initCallName = "_ctor";
              initCallTok = rr.Tok;
            }
            var cl = (rr.EType as UserDefinedType)?.ResolvedClass as NonNullTypeDecl;
            if (cl == null || rr.EType.IsTraitType) {
              ReportError(rr.tok, "new can be applied only to class types (got {0})", rr.EType);
            } else {
              // ---------- new C.Init(EE)
              Contract.Assert(initCallName != null);
              var prevErrorCount = ErrorCount;

              // We want to create a MemberSelectExpr for the initializing method.  To do that, we create a throw-away receiver of the appropriate
              // type, create a dot-suffix expression around this receiver, and then resolve it in the usual way for dot-suffix expressions.
              // It is important that this throw-away receiver have its .PreType filled in, because the call to ResolveDotSuffix will recursive
              // down to resolve this "lhs"; that's a no-op if the .PreType is already filled in, whereas it could cause a "'this' not allowed in
              // static context" error if the code tried to resolve this "this" against the enclosing environment.
              var lhs = new ImplicitThisExpr_ConstructorCall(initCallTok) {
                Type = rr.EType,
                PreType = Type2PreType(rr.EType)
              };
              var callLhs = new ExprDotName(((UserDefinedType)rr.EType).tok, lhs, initCallName, ret == null ? null : ret.LastComponent.OptTypeArguments);
              ResolveDotSuffix(callLhs, true, rr.Bindings.ArgumentBindings, resolutionContext, true);
              if (prevErrorCount == ErrorCount) {
                Contract.Assert(callLhs.ResolvedExpression is MemberSelectExpr);  // since ResolveApplySuffix succeeded and call.Lhs denotes an expression (not a module or a type)
                var methodSel = (MemberSelectExpr)callLhs.ResolvedExpression;
                if (methodSel.Member is Method) {
                  rr.InitCall = new CallStmt(stmt.RangeToken, new List<Expression>(), methodSel, rr.Bindings.ArgumentBindings, initCallTok);
                  ResolveCallStmt(rr.InitCall, resolutionContext, rr.EType);
                  if (rr.InitCall.Method is Constructor) {
                    callsConstructor = true;
                  }
                } else {
                  ReportError(initCallTok, "object initialization must denote an initializing method or constructor ({0})", initCallName);
                }
              }
            }
        }
        if (rr.EType.IsRefType) {
          var udt = rr.EType.NormalizeExpand() as UserDefinedType;
          if (udt != null) {
            var cl = (ClassDecl)udt.ResolvedClass;  // cast is guaranteed by the call to rr.EType.IsRefType above, together with the "rr.EType is UserDefinedType" test
            if (!callsConstructor && !cl.IsObjectTrait && !udt.IsArrayType && (cl.HasConstructor || cl.EnclosingModuleDefinition != currentClass.EnclosingModuleDefinition)) {
              ReportError(stmt, "when allocating an object of {1}type '{0}', one of its constructor methods must be called", cl.Name,
                cl.HasConstructor ? "" : "imported ");
            }
          }
        }
        rr.PreType = Type2PreType(rr.EType);
      }
    }

    /// <summary>
    /// Checks if lhs, which is expected to be a successfully resolved expression, denotes something
    /// that can be assigned to.  In particular, this means that lhs denotes a mutable variable, field,
    /// or array element.  If a violation is detected, an error is reported.
    /// </summary>
    void CheckIsLvalue(Expression lhs, ResolutionContext resolutionContext) {
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
          var cf = field as ConstantField;
          if (inBodyInitContext && cf != null && !cf.IsStatic && cf.Rhs == null) {
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
        var arrayType = resolver.ResolvedArrayType(ll.Seq.tok, 1, new InferredTypeProxy(), resolutionContext, true);
        AddSubtypeConstraint(Type2PreType(arrayType), ll.Seq.PreType, ll.Seq.tok, "LHS of array assignment must denote an array element (found {1})");
        if (!ll.SelectOne) {
          ReportError(ll.Seq, "cannot assign to a range of array elements (try the 'forall' statement)");
        }
      } else if (lhs is MultiSelectExpr) {
        // nothing to check; this can only denote an array element
      } else {
        ReportError(lhs, "LHS of assignment must denote a mutable variable or field");
      }
    }

    void ResolveAlternatives(List<GuardedAlternative> alternatives, AlternativeLoopStmt loopToCatchBreaks, ResolutionContext resolutionContext) {
      Contract.Requires(alternatives != null);
      Contract.Requires(resolutionContext != null);

      // first, resolve the guards
      foreach (var alternative in alternatives) {
        ResolveExpression(alternative.Guard, resolutionContext);
        alternative.Guard.PreType = ConstrainResultToBoolFamily(alternative.Guard.tok, "if/while case", "condition is expected to be of type bool, but is {0}");
      }

      if (loopToCatchBreaks != null) {
        loopStack.Add(loopToCatchBreaks);  // push
      }
      foreach (var alternative in alternatives) {
        scope.PushMarker();
        dominatingStatementLabels.PushMarker();
        if (alternative.IsBindingGuard) {
          var exists = (ExistsExpr)alternative.Guard;
          foreach (var v in exists.BoundVars) {
            ScopePushAndReport(v, "bound-variable", false);
          }
        }
        ResolveAttributes(alternative, resolutionContext, false);
        foreach (Statement ss in alternative.Body) {
          ResolveStatementWithLabels(ss, resolutionContext);
        }
        dominatingStatementLabels.PopMarker();
        scope.PopMarker();
      }
      if (loopToCatchBreaks != null) {
        loopStack.RemoveAt(loopStack.Count - 1);  // pop
      }
    }
  }
}
