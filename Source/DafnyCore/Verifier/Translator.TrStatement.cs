using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;
using Bpl = Microsoft.Boogie;
using BplParser = Microsoft.Boogie.Parser;
using static Microsoft.Dafny.Util;
using PODesc = Microsoft.Dafny.ProofObligationDescription;

namespace Microsoft.Dafny {
  public partial class Translator {
    private void TrStmt(Statement stmt, BoogieStmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran) {
      Contract.Requires(stmt != null);
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);
      Contract.Requires(codeContext != null && predef != null);
      Contract.Ensures(fuelContext == Contract.OldValue(fuelContext));

      stmtContext = StmtType.NONE;
      adjustFuelForExists = true;  // fuel for exists might need to be adjusted based on whether it's in an assert or assume stmt.
      if (stmt is PredicateStmt predicateStmt) {
        TrPredicateStmt(predicateStmt, builder, locals, etran);

      } else if (stmt is PrintStmt) {
        AddComment(builder, stmt, "print statement");
        PrintStmt s = (PrintStmt)stmt;
        foreach (var arg in s.Args) {
          TrStmt_CheckWellformed(arg, builder, locals, etran, false);
        }

      } else if (stmt is RevealStmt) {
        AddComment(builder, stmt, "reveal statement");
        var s = (RevealStmt)stmt;
        foreach (var la in s.LabeledAsserts) {
          Contract.Assert(la.E != null);  // this should have been filled in by now
          builder.Add(new Bpl.AssumeCmd(s.Tok, la.E));
        }
        TrStmtList(s.ResolvedStatements, builder, locals, etran);

      } else if (stmt is BreakStmt) {
        var s = (BreakStmt)stmt;
        AddComment(builder, stmt, $"{s.Kind} statement");
        var lbl = (s.IsContinue ? "continue_" : "after_") + s.TargetStmt.Labels.Data.AssignUniqueId(CurrentIdGenerator);
        builder.Add(new GotoCmd(s.Tok, new List<string> { lbl }));
      } else if (stmt is ReturnStmt) {
        var s = (ReturnStmt)stmt;
        AddComment(builder, stmt, "return statement");
        if (s.ReverifyPost) {
          // $_reverifyPost := true;
          builder.Add(Bpl.Cmd.SimpleAssign(s.Tok, new Bpl.IdentifierExpr(s.Tok, "$_reverifyPost", Bpl.Type.Bool), Bpl.Expr.True));
        }
        if (s.HiddenUpdate != null) {
          TrStmt(s.HiddenUpdate, builder, locals, etran);
        }
        if (codeContext is IMethodCodeContext) {
          var method = (IMethodCodeContext)codeContext;
          method.Outs.Iter(p => CheckDefiniteAssignmentReturn(stmt.Tok, p, builder));
        }
        builder.Add(new Bpl.ReturnCmd(stmt.Tok));
      } else if (stmt is YieldStmt) {
        var s = (YieldStmt)stmt;
        AddComment(builder, s, "yield statement");
        Contract.Assert(codeContext is IteratorDecl);
        var iter = (IteratorDecl)codeContext;
        // if the yield statement has arguments, do them first
        if (s.HiddenUpdate != null) {
          TrStmt(s.HiddenUpdate, builder, locals, etran);
        }
        // this.ys := this.ys + [this.y];
        var th = new ThisExpr(iter);
        Contract.Assert(iter.OutsFields.Count == iter.OutsHistoryFields.Count);
        for (int i = 0; i < iter.OutsFields.Count; i++) {
          var y = iter.OutsFields[i];
          var dafnyY = new MemberSelectExpr(s.Tok, th, y);
          var ys = iter.OutsHistoryFields[i];
          var dafnyYs = new MemberSelectExpr(s.Tok, th, ys);
          var dafnySingletonY = new SeqDisplayExpr(s.Tok, new List<Expression>() { dafnyY });
          dafnySingletonY.Type = ys.Type;  // resolve here
          var rhs = new BinaryExpr(s.Tok, BinaryExpr.Opcode.Add, dafnyYs, dafnySingletonY);
          rhs.ResolvedOp = BinaryExpr.ResolvedOpcode.Concat;
          rhs.Type = ys.Type;  // resolve here
          var cmd = Bpl.Cmd.SimpleAssign(s.Tok, etran.HeapCastToIdentifierExpr,
            ExpressionTranslator.UpdateHeap(s.Tok, etran.HeapExpr, etran.TrExpr(th), new Bpl.IdentifierExpr(s.Tok, GetField(ys)), etran.TrExpr(rhs)));
          builder.Add(cmd);
        }
        // yieldCount := yieldCount + 1;  assume yieldCount == |ys|;
        var yc = new Bpl.IdentifierExpr(s.Tok, yieldCountVariable);
        var incYieldCount = Bpl.Cmd.SimpleAssign(s.Tok, yc, Bpl.Expr.Binary(s.Tok, Bpl.BinaryOperator.Opcode.Add, yc, Bpl.Expr.Literal(1)));
        builder.Add(incYieldCount);
        builder.Add(TrAssumeCmd(s.Tok, YieldCountAssumption(iter, etran)));
        // assume $IsGoodHeap($Heap);
        builder.Add(AssumeGoodHeap(s.Tok, etran));
        // assert YieldEnsures[subst];  // where 'subst' replaces "old(E)" with "E" being evaluated in $_OldIterHeap
        var yeEtran = new ExpressionTranslator(this, predef, etran.HeapExpr, new Bpl.IdentifierExpr(s.Tok, "$_OldIterHeap", predef.HeapType));
        foreach (var p in iter.YieldEnsures) {
          bool splitHappened;  // actually, we don't care
          var ss = TrSplitExpr(p.E, yeEtran, true, out splitHappened);
          foreach (var split in ss) {
            if (RefinementToken.IsInherited(split.Tok, currentModule)) {
              // this postcondition was inherited into this module, so just ignore it
            } else if (split.IsChecked) {
              var yieldToken = new NestedToken(s.Tok, split.Tok);
              var desc = new PODesc.YieldEnsures();
              builder.Add(AssertNS(yieldToken, split.E, desc, stmt.Tok, null));
            }
          }
          builder.Add(TrAssumeCmd(stmt.Tok, yeEtran.TrExpr(p.E)));
        }
        YieldHavoc(iter.tok, iter, builder, etran);
        builder.AddCaptureState(s);

      } else if (stmt is AssignSuchThatStmt) {
        var s = (AssignSuchThatStmt)stmt;
        AddComment(builder, s, "assign-such-that statement");
        // Essentially, treat like an assert (that values for the LHS exist), a havoc (of the LHS), and an
        // assume (of the RHS).  However, we also need to check the well-formedness of the LHS and RHS.
        // The well-formedness of the LHS is done by the havoc. The well-formedness of the RHS is most
        // easily done after that havoc, but we need to be careful about two things:
        //   - We should not generate any errors for uses of LHSs. This is not an issue for fields or
        //     array elements, because they already have values before reaching the assign-such-that statement.
        //     (Note, "this.f" is not allowed as a LHS in the first division of a constructor.)
        //     For any local variable or out-parameter x that's a LHS, we create a new variable x' and
        //     substitute x' for x in the RHS before doing the well-formedness check.
        //   - The well-formedness checks need to be able to assume that each x' has a value of its
        //     type. However, this assumption must not carry over to the existence assertion, because
        //     then everything will be provable if x' is of a known-empty type. Instead, the well-formedness
        //     check is wrapped inside an "if" whose guard is the type antecedent. After the existence
        //     check, the type antecedent is assumed of the original x, the RHS is assumed, and x is
        //     marked off has having been definitely assigned.
        //
        // So, the Dafny statement
        //     E.f, x :| RHS(x);
        // is translated into the following Boogie code:
        //     var x';
        //     Tr[[ E.f := *; ]]  // this havoc is translated like a Dafny assignment statement, which means
        //                        // the well-formedness of E is checked here
        //     if (typeAntecedent(x')) {
        //       check well-formedness of RHS(x');
        //     }
        //     assert (exists x'' :: RHS(x''));  // for ":| assume", omit this line; for ":|", LHS is only allowed to contain simple variables
        //     defass#x := true;
        //     havoc x;
        //     assume RHS(x);

        var simpleLHSs = new List<IdentifierExpr>();
        Bpl.Expr typeAntecedent = Bpl.Expr.True;
        var havocLHSs = new List<Expression>();
        var havocRHSs = new List<AssignmentRhs>();
        var substMap = new Dictionary<IVariable, Expression>();
        foreach (var lhs in s.Lhss) {
          var lvalue = lhs.Resolved;
          if (lvalue is IdentifierExpr ide) {
            simpleLHSs.Add(ide);
            var wh = SetupVariableAsLocal(ide.Var, substMap, builder, locals, etran);
            typeAntecedent = BplAnd(typeAntecedent, wh);
          } else {
            havocLHSs.Add(lhs.Resolved);
            havocRHSs.Add(new HavocRhs(lhs.tok));  // note, a HavocRhs is constructed as already resolved
          }
        }
        ProcessLhss(havocLHSs, false, true, builder, locals, etran, out var lhsBuilder, out var bLhss, out _, out _, out _);
        ProcessRhss(lhsBuilder, bLhss, havocLHSs, havocRHSs, builder, locals, etran);

        // Here comes the well-formedness check
        var wellFormednessBuilder = new BoogieStmtListBuilder(this);
        var rhs = Substitute(s.Expr, null, substMap);
        TrStmt_CheckWellformed(rhs, wellFormednessBuilder, locals, etran, false);
        var ifCmd = new Bpl.IfCmd(s.Tok, typeAntecedent, wellFormednessBuilder.Collect(s.Tok), null, null);
        builder.Add(ifCmd);

        // Here comes the assert part
        if (s.AssumeToken == null) {
          substMap = new Dictionary<IVariable, Expression>();
          var bvars = new List<BoundVar>();
          foreach (var lhs in s.Lhss) {
            var l = lhs.Resolved;
            if (l is IdentifierExpr x) {
              CloneVariableAsBoundVar(x.tok, x.Var, "$as#" + x.Name, out var bv, out var ie);
              bvars.Add(bv);
              substMap.Add(x.Var, ie);
            } else {
              // other forms of LHSs have been ruled out by the resolver (it would be possible to
              // handle them, but it would involve heap-update expressions--the translation would take
              // effort, and it's not certain that the existential would be successful in verification).
              Contract.Assume(false);  // unexpected case
            }
          }

          GenerateAndCheckGuesses(s.Tok, bvars, s.Bounds, Substitute(s.Expr, null, substMap), TrTrigger(etran, s.Attributes, s.Tok, substMap), builder, etran);
        }

        // Mark off the simple variables as having definitely been assigned AND THEN havoc their values. By doing them
        // in this order, they type antecedents will in effect be assumed.
        var bHavocLHSs = new List<Bpl.IdentifierExpr>();
        foreach (var lhs in simpleLHSs) {
          MarkDefiniteAssignmentTracker(lhs, builder);
          bHavocLHSs.Add((Bpl.IdentifierExpr)etran.TrExpr(lhs));
        }
        builder.Add(new Bpl.HavocCmd(s.Tok, bHavocLHSs));

        // End by doing the assume
        builder.Add(TrAssumeCmd(s.Tok, etran.TrExpr(s.Expr)));
        builder.AddCaptureState(s);  // just do one capture state--here, at the very end (that is, don't do one before the assume)

      } else if (stmt is UpdateStmt) {
        var s = (UpdateStmt)stmt;
        // This UpdateStmt can be single-target assignment, a multi-assignment, a call statement, or
        // an array-range update.  Handle the multi-assignment here and handle the others as for .ResolvedStatements.
        var resolved = s.ResolvedStatements;
        if (resolved.Count == 1) {
          TrStmt(resolved[0], builder, locals, etran);
        } else {
          AddComment(builder, s, "update statement");
          var lhss = new List<Expression>();
          foreach (var lhs in s.Lhss) {
            lhss.Add(lhs.Resolved);
          }
          List<AssignToLhs> lhsBuilder;
          List<Bpl.IdentifierExpr> bLhss;
          // note: because we have more than one expression, we always must assign to Boogie locals in a two
          // phase operation. Thus rhssCanAffectPreviouslyKnownExpressions is just true.
          Contract.Assert(1 < lhss.Count);

          Bpl.Expr[] lhsObjs, lhsFields;
          string[] lhsNames;
          ProcessLhss(lhss, true, false, builder, locals, etran, out lhsBuilder, out bLhss, out lhsObjs, out lhsFields, out lhsNames);
          // We know that, because the translation saves to a local variable, that the RHS always need to
          // generate a new local, i.e. bLhss is just all nulls.
          Contract.Assert(Contract.ForAll(bLhss, lhs => lhs == null));
          // This generates the assignments, and gives them to us as finalRhss.
          var finalRhss = ProcessUpdateAssignRhss(lhss, s.Rhss, builder, locals, etran);
          // ProcessLhss has laid down framing conditions and the ProcessUpdateAssignRhss will check subranges (nats),
          // but we need to generate the distinctness condition (two LHS are equal only when the RHS is also
          // equal). We need both the LHS and the RHS to do this, which is why we need to do it here.
          CheckLhssDistinctness(finalRhss, s.Rhss, lhss, builder, etran, lhsObjs, lhsFields, lhsNames, s.OriginalInitialLhs);
          // Now actually perform the assignments to the LHS.
          for (int i = 0; i < lhss.Count; i++) {
            lhsBuilder[i](finalRhss[i], s.Rhss[i] is HavocRhs, builder, etran);
          }
          builder.AddCaptureState(s);
        }

      } else if (stmt is AssignOrReturnStmt) {
        AddComment(builder, stmt, "assign-or-return statement (:-)");
        AssignOrReturnStmt s = (AssignOrReturnStmt)stmt;
        TrStmtList(s.ResolvedStatements, builder, locals, etran);

      } else if (stmt is AssignStmt) {
        AddComment(builder, stmt, "assignment statement");
        AssignStmt s = (AssignStmt)stmt;
        TrAssignment(stmt, s.Lhs.Resolved, s.Rhs, builder, locals, etran);

      } else if (stmt is CallStmt) {
        AddComment(builder, stmt, "call statement");
        TrCallStmt((CallStmt)stmt, builder, locals, etran, null);

      } else if (stmt is DividedBlockStmt) {
        var s = (DividedBlockStmt)stmt;
        AddComment(builder, stmt, "divided block before new;");
        var prevDefiniteAssignmentTrackerCount = definiteAssignmentTrackers.Count;
        var tok = s.SeparatorTok ?? s.Tok;
        // a DividedBlockStmt occurs only inside a Constructor body of a class
        var cl = (ClassDecl)((Constructor)codeContext).EnclosingClass;
        var fields = Concat(cl.InheritedMembers, cl.Members).ConvertAll(member =>
          member is Field && !member.IsStatic && !member.IsInstanceIndependentConstant ? (Field)member : null);
        fields.RemoveAll(f => f == null);
        var localSurrogates = fields.ConvertAll(f => new Bpl.LocalVariable(f.tok, new TypedIdent(f.tok, SurrogateName(f), TrType(f.Type))));
        locals.AddRange(localSurrogates);
        fields.Iter(f => AddDefiniteAssignmentTrackerSurrogate(f, cl, locals, codeContext is Constructor && codeContext.IsGhost));

        Contract.Assert(!inBodyInitContext);
        inBodyInitContext = true;
        TrStmtList(s.BodyInit, builder, locals, etran);
        Contract.Assert(inBodyInitContext);
        inBodyInitContext = false;

        // The "new;" translates into an allocation of "this"
        AddComment(builder, stmt, "new;");
        fields.Iter(f => CheckDefiniteAssignmentSurrogate(s.SeparatorTok ?? s.RangeToken.EndToken, f, true, builder));
        fields.Iter(RemoveDefiniteAssignmentTrackerSurrogate);
        var th = new ThisExpr(cl);
        var bplThis = (Bpl.IdentifierExpr)etran.TrExpr(th);
        SelectAllocateObject(tok, bplThis, th.Type, false, builder, etran);
        for (int i = 0; i < fields.Count; i++) {
          // assume $Heap[this, f] == this.f;
          var mse = new MemberSelectExpr(tok, th, fields[i]);
          Bpl.Expr surr = new Bpl.IdentifierExpr(tok, localSurrogates[i]);
          surr = CondApplyUnbox(tok, surr, fields[i].Type, mse.Type);
          builder.Add(new Bpl.AssumeCmd(tok, Bpl.Expr.Eq(etran.TrExpr(mse), surr)));
        }
        CommitAllocatedObject(tok, bplThis, null, builder, etran);

        AddComment(builder, stmt, "divided block after new;");
        TrStmtList(s.BodyProper, builder, locals, etran);
        RemoveDefiniteAssignmentTrackers(s.Body, prevDefiniteAssignmentTrackerCount);

      } else if (stmt is BlockStmt) {
        var s = (BlockStmt)stmt;
        var prevDefiniteAssignmentTrackerCount = definiteAssignmentTrackers.Count;
        TrStmtList(s.Body, builder, locals, etran);
        RemoveDefiniteAssignmentTrackers(s.Body, prevDefiniteAssignmentTrackerCount);

      } else if (stmt is IfStmt ifStmt) {
        TrIfStmt(ifStmt, builder, locals, etran);

      } else if (stmt is AlternativeStmt) {
        AddComment(builder, stmt, "alternative statement");
        var s = (AlternativeStmt)stmt;
        var elseCase = Assert(s.Tok, Bpl.Expr.False, new PODesc.AlternativeIsComplete());
        TrAlternatives(s.Alternatives, elseCase, null, builder, locals, etran, stmt.IsGhost);

      } else if (stmt is WhileStmt whileStmt) {
        TrWhileStmt(whileStmt, builder, locals, etran);

      } else if (stmt is AlternativeLoopStmt) {
        AddComment(builder, stmt, "alternative loop statement");
        var s = (AlternativeLoopStmt)stmt;
        var tru = new LiteralExpr(s.Tok, true);
        tru.Type = Type.Bool; // resolve here
        TrLoop(s, tru,
          delegate (BoogieStmtListBuilder bld, ExpressionTranslator e) {
            TrAlternatives(s.Alternatives, null, new Bpl.BreakCmd(s.Tok, null), bld, locals, e, stmt.IsGhost);
            InsertContinueTarget(s, bld);
          },
          builder, locals, etran);

      } else if (stmt is ForLoopStmt forLoopStmt) {
        TrForLoop(forLoopStmt, builder, locals, etran);

      } else if (stmt is ModifyStmt) {
        AddComment(builder, stmt, "modify statement");
        var s = (ModifyStmt)stmt;
        // check well-formedness of the modifies clauses
        CheckFrameWellFormed(new WFOptions(), s.Mod.Expressions, locals, builder, etran);
        // check that the modifies is a subset
        CheckFrameSubset(s.Tok, s.Mod.Expressions, null, null, etran, builder, new PODesc.FrameSubset("modify statement", true), null);
        // cause the change of the heap according to the given frame
        var suffix = CurrentIdGenerator.FreshId("modify#");
        string modifyFrameName = "$Frame$" + suffix;
        var preModifyHeapVar = new Bpl.LocalVariable(s.Tok, new Bpl.TypedIdent(s.Tok, "$PreModifyHeap$" + suffix, predef.HeapType));
        locals.Add(preModifyHeapVar);
        DefineFrame(s.Tok, s.Mod.Expressions, builder, locals, modifyFrameName);
        if (s.Body == null) {
          var preModifyHeap = new Bpl.IdentifierExpr(s.Tok, preModifyHeapVar);
          // preModifyHeap := $Heap;
          builder.Add(Bpl.Cmd.SimpleAssign(s.Tok, preModifyHeap, etran.HeapExpr));
          // havoc $Heap;
          builder.Add(new Bpl.HavocCmd(s.Tok, new List<Bpl.IdentifierExpr> { etran.HeapCastToIdentifierExpr }));
          // assume $HeapSucc(preModifyHeap, $Heap);   OR $HeapSuccGhost
          builder.Add(TrAssumeCmd(s.Tok, HeapSucc(preModifyHeap, etran.HeapExpr, s.IsGhost)));
          // assume nothing outside the frame was changed
          var etranPreLoop = new ExpressionTranslator(this, predef, preModifyHeap);
          var updatedFrameEtran = new ExpressionTranslator(etran, modifyFrameName);
          builder.Add(TrAssumeCmd(s.Tok, FrameConditionUsingDefinedFrame(s.Tok, etranPreLoop, etran, updatedFrameEtran)));
        } else {
          // do the body, but with preModifyHeapVar as the governing frame
          var updatedFrameEtran = new ExpressionTranslator(etran, modifyFrameName);
          CurrentIdGenerator.Push();
          TrStmt(s.Body, builder, locals, updatedFrameEtran);
          CurrentIdGenerator.Pop();
        }
        builder.AddCaptureState(stmt);

      } else if (stmt is ForallStmt) {
        var s = (ForallStmt)stmt;
        this.fuelContext = FuelSetting.ExpandFuelContext(stmt.Attributes, stmt.Tok, this.fuelContext, this.reporter);

        CurrentIdGenerator.Push();
        if (s.Kind == ForallStmt.BodyKind.Assign) {
          AddComment(builder, stmt, "forall statement (assign)");
          Contract.Assert(s.Ens.Count == 0);
          if (s.BoundVars.Count == 0) {
            TrStmt(s.Body, builder, locals, etran);
          } else {
            var s0 = (AssignStmt)s.S0;
            var definedness = new BoogieStmtListBuilder(this);
            var updater = new BoogieStmtListBuilder(this);
            DefineFuelConstant(stmt.Tok, stmt.Attributes, definedness, etran);
            TrForallAssign(s, s0, definedness, updater, locals, etran);
            // All done, so put the two pieces together
            builder.Add(new Bpl.IfCmd(s.Tok, null, definedness.Collect(s.Tok), null, updater.Collect(s.Tok)));
            builder.AddCaptureState(stmt);
          }

        } else if (s.Kind == ForallStmt.BodyKind.Call) {
          AddComment(builder, stmt, "forall statement (call)");
          Contract.Assert(s.Ens.Count == 0);
          if (s.BoundVars.Count == 0) {
            Contract.Assert(LiteralExpr.IsTrue(s.Range));  // follows from the invariant of ForallStmt
            TrStmt(s.Body, builder, locals, etran);
          } else {
            var s0 = (CallStmt)s.S0;
            if (Attributes.Contains(s.Attributes, "_trustWellformed")) {
              TrForallStmtCall(s.Tok, s.BoundVars, s.Bounds, s.Range, null, s.ForallExpressions, s0, null, builder, locals, etran);
            } else {
              var definedness = new BoogieStmtListBuilder(this);
              DefineFuelConstant(stmt.Tok, stmt.Attributes, definedness, etran);
              var exporter = new BoogieStmtListBuilder(this);
              TrForallStmtCall(s.Tok, s.BoundVars, s.Bounds, s.Range, null, s.ForallExpressions, s0, definedness, exporter, locals, etran);
              // All done, so put the two pieces together
              builder.Add(new Bpl.IfCmd(s.Tok, null, definedness.Collect(s.Tok), null, exporter.Collect(s.Tok)));
            }
            builder.AddCaptureState(stmt);
          }

        } else if (s.Kind == ForallStmt.BodyKind.Proof) {
          AddComment(builder, stmt, "forall statement (proof)");
          var definedness = new BoogieStmtListBuilder(this);
          var exporter = new BoogieStmtListBuilder(this);
          DefineFuelConstant(stmt.Tok, stmt.Attributes, definedness, etran);
          TrForallProof(s, definedness, exporter, locals, etran);
          // All done, so put the two pieces together
          builder.Add(new Bpl.IfCmd(s.Tok, null, definedness.Collect(s.Tok), null, exporter.Collect(s.Tok)));
          builder.AddCaptureState(stmt);

        } else {
          Contract.Assert(false);  // unexpected kind
        }
        CurrentIdGenerator.Pop();
        this.fuelContext = FuelSetting.PopFuelContext();

      } else if (stmt is CalcStmt calcStmt) {
        TrCalcStmt(calcStmt, builder, locals, etran);

      } else if (stmt is NestedMatchStmt nestedMatchStmt) {
        TrStmt(nestedMatchStmt.Flattened, builder, locals, etran);
      } else if (stmt is MatchStmt matchStmt) {
        TrMatchStmt(matchStmt, builder, locals, etran);
      } else if (stmt is VarDeclStmt) {
        var s = (VarDeclStmt)stmt;
        var newLocalIds = new List<Bpl.IdentifierExpr>();
        int i = 0;
        foreach (var local in s.Locals) {
          Bpl.Type varType = TrType(local.Type);
          Bpl.Expr wh = GetWhereClause(local.Tok,
            new Bpl.IdentifierExpr(local.Tok, local.AssignUniqueName(currentDeclaration.IdGenerator), varType),
            local.Type, etran, isAllocContext.Var(stmt.IsGhost, local));
          // if needed, register definite-assignment tracking for this local
          var needDefiniteAssignmentTracking = s.Update == null || s.Update is AssignSuchThatStmt;
          if (s.Update is UpdateStmt) {
            // there is an initial assignment, but we need to look out for "*" being that assignment
            var us = (UpdateStmt)s.Update;
            if (i < us.Rhss.Count && us.Rhss[i] is HavocRhs) {
              needDefiniteAssignmentTracking = true;
            }
          }
          if (!local.Type.IsNonempty) {
            // This prevents generating an unsatisfiable where clause for possibly empty types
            needDefiniteAssignmentTracking = true;
          }
          if (needDefiniteAssignmentTracking) {
            var defassExpr = AddDefiniteAssignmentTracker(local, locals);
            if (wh != null && defassExpr != null) {
              // make the "where" expression be "defass ==> wh", because we don't want to assume anything
              // before the variable has been assigned (for a variable that needs definite-assignment tracking
              // in the first place)
              wh = BplImp(defassExpr, wh);
            }
          }
          // create the variable itself (now that "wh" may mention the definite-assignment tracker)
          Bpl.LocalVariable var = new Bpl.LocalVariable(local.Tok, new Bpl.TypedIdent(local.Tok, local.AssignUniqueName(currentDeclaration.IdGenerator), varType, wh));
          var.Attributes = etran.TrAttributes(local.Attributes, null);
          newLocalIds.Add(new Bpl.IdentifierExpr(local.Tok, var));
          locals.Add(var);
          i++;
        }
        if (s.Update == null) {
          // it is necessary to do a havoc here in order to give the variable the correct allocation state
          builder.Add(new HavocCmd(s.Tok, newLocalIds));
        }
        // processing of "assumption" variables happens after the variable is possibly havocked above
        foreach (var local in s.Locals) {
          if (Attributes.Contains(local.Attributes, "assumption")) {
            Bpl.Type varType = TrType(local.Type);
            builder.Add(new AssumeCmd(local.Tok, new Bpl.IdentifierExpr(local.Tok, local.AssignUniqueName(currentDeclaration.IdGenerator), varType), new QKeyValue(local.Tok, "assumption_variable_initialization", new List<object>(), null)));
          }
        }
        if (s.Update != null) {
          TrStmt(s.Update, builder, locals, etran);
        }
      } else if (stmt is VarDeclPattern) {
        var s = (VarDeclPattern)stmt;
        foreach (var local in s.LocalVars) {
          Bpl.LocalVariable bvar = new Bpl.LocalVariable(local.Tok, new Bpl.TypedIdent(local.Tok, local.AssignUniqueName(currentDeclaration.IdGenerator), TrType(local.Type)));
          locals.Add(bvar);
          var bIe = new Bpl.IdentifierExpr(bvar.tok, bvar);
          builder.Add(new Bpl.HavocCmd(local.Tok, new List<Bpl.IdentifierExpr> { bIe }));
          Bpl.Expr wh = GetWhereClause(local.Tok, bIe, local.Type, etran, isAllocContext.Var(stmt.IsGhost, local));
          if (wh != null) {
            builder.Add(TrAssumeCmd(local.Tok, wh));
          }
        }
        var varNameGen = CurrentIdGenerator.NestedFreshIdGenerator("let#");
        var pat = s.LHS;
        var rhs = s.RHS;
        var nm = varNameGen.FreshId(string.Format("#{0}#", 0));
        var r = new Bpl.LocalVariable(pat.tok, new Bpl.TypedIdent(pat.tok, nm, TrType(rhs.Type)));
        locals.Add(r);
        var rIe = new Bpl.IdentifierExpr(rhs.tok, r);
        CheckWellformedWithResult(rhs, new WFOptions(null, false, false), rIe, pat.Expr.Type, locals, builder, etran);
        CheckCasePatternShape(pat, rIe, rhs.tok, pat.Expr.Type, builder);
        builder.Add(TrAssumeCmd(pat.tok, Bpl.Expr.Eq(etran.TrExpr(pat.Expr), rIe)));
      } else if (stmt is TryRecoverStatement haltRecoveryStatement) {
        // try/recover statements are currently internal-only AST nodes that cannot be
        // directly used in user Dafny code. They are only generated by rewriters, and verifying
        // their use is low value.
        throw new NotSupportedException("Verification of try/recover statements is not supported");
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected statement
      }
    }

    private void TrPredicateStmt(PredicateStmt stmt, BoogieStmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran) {
      Contract.Requires(stmt != null);
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);

      var stmtBuilder = new BoogieStmtListBuilder(this);
      string errorMessage = CustomErrorMessage(stmt.Attributes);
      this.fuelContext = FuelSetting.ExpandFuelContext(stmt.Attributes, stmt.Tok, this.fuelContext, this.reporter);
      var defineFuel = DefineFuelConstant(stmt.Tok, stmt.Attributes, stmtBuilder, etran);
      var b = defineFuel ? stmtBuilder : builder;
      if (stmt is AssertStmt || DafnyOptions.O.DisallowSoundnessCheating) {
        stmtContext = StmtType.ASSERT;
        AddComment(b, stmt, "assert statement");
        TrStmt_CheckWellformed(stmt.Expr, b, locals, etran, false);
        IToken enclosingToken = null;
        if (Attributes.Contains(stmt.Attributes, "_prependAssertToken")) {
          enclosingToken = stmt.Tok;
        }
        BoogieStmtListBuilder proofBuilder = null;
        var assertStmt = stmt as AssertStmt;
        if (assertStmt != null) {
          if (assertStmt.Proof != null) {
            proofBuilder = new BoogieStmtListBuilder(this);
            AddComment(proofBuilder, stmt, "assert statement proof");
            CurrentIdGenerator.Push();
            TrStmt(((AssertStmt)stmt).Proof, proofBuilder, locals, etran);
            CurrentIdGenerator.Pop();
          } else if (assertStmt.Label != null) {
            proofBuilder = new BoogieStmtListBuilder(this);
            AddComment(proofBuilder, stmt, "assert statement proof");
          }
        }

        bool splitHappened;
        var ss = TrSplitExpr(stmt.Expr, etran, true, out splitHappened);
        if (!splitHappened) {
          var tok = enclosingToken == null ? GetToken(stmt.Expr) : new NestedToken(enclosingToken, GetToken(stmt.Expr));
          var desc = new PODesc.AssertStatement(errorMessage);
          (proofBuilder ?? b).Add(Assert(tok, etran.TrExpr(stmt.Expr), desc, stmt.Tok,
            etran.TrAttributes(stmt.Attributes, null)));
        } else {
          foreach (var split in ss) {
            if (split.IsChecked) {
              var tok = enclosingToken == null ? split.E.tok : new NestedToken(enclosingToken, split.Tok);
              var desc = new PODesc.AssertStatement(errorMessage);
              (proofBuilder ?? b).Add(AssertNS(ToDafnyToken(tok), split.E, desc, stmt.Tok,
                etran.TrAttributes(stmt.Attributes, null))); // attributes go on every split
            }
          }
        }
        if (proofBuilder != null) {
          PathAsideBlock(stmt.Tok, proofBuilder, b);
        }
        stmtContext = StmtType.NONE; // done with translating assert stmt
        if (splitHappened || proofBuilder != null) {
          if (assertStmt != null && assertStmt.Label != null) {
            // make copies of the variables used in the assertion
            var name = "$Heap_at_" + assertStmt.Label.AssignUniqueId(CurrentIdGenerator);
            var heapAt = new Bpl.LocalVariable(stmt.Tok, new Bpl.TypedIdent(stmt.Tok, name, predef.HeapType));
            locals.Add(heapAt);
            var h = new Bpl.IdentifierExpr(stmt.Tok, heapAt);
            b.Add(Bpl.Cmd.SimpleAssign(stmt.Tok, h, etran.HeapExpr));
            var substMap = new Dictionary<IVariable, Expression>();
            foreach (var v in FreeVariablesUtil.ComputeFreeVariables(assertStmt.Expr)) {
              if (v is LocalVariable) {
                var vcopy = new LocalVariable(stmt.RangeToken, string.Format("##{0}#{1}", name, v.Name), v.Type, v.IsGhost);
                vcopy.type = vcopy.OptionalType; // resolve local here
                IdentifierExpr ie = new IdentifierExpr(vcopy.Tok, vcopy.AssignUniqueName(currentDeclaration.IdGenerator));
                ie.Var = vcopy;
                ie.Type = ie.Var.Type; // resolve ie here
                substMap.Add(v, ie);
                locals.Add(new Bpl.LocalVariable(vcopy.Tok,
                  new Bpl.TypedIdent(vcopy.Tok, vcopy.AssignUniqueName(currentDeclaration.IdGenerator), TrType(vcopy.Type))));
                b.Add(Bpl.Cmd.SimpleAssign(stmt.Tok, TrVar(stmt.Tok, vcopy), TrVar(stmt.Tok, v)));
              }
            }
            var exprToBeRevealed = Substitute(assertStmt.Expr, null, substMap);
            var etr = new ExpressionTranslator(etran, h);
            assertStmt.Label.E = etr.TrExpr(exprToBeRevealed);
          } else if (!defineFuel) {
            // Adding the assume stmt, resetting the stmtContext
            stmtContext = StmtType.ASSUME;
            adjustFuelForExists = true;
            b.Add(TrAssumeCmd(stmt.Tok, etran.TrExpr(stmt.Expr)));
            stmtContext = StmtType.NONE;
          }
        }
        if (defineFuel) {
          var ifCmd = new Bpl.IfCmd(stmt.Tok, null, b.Collect(stmt.Tok), null,
            null); // BUGBUG: shouldn't this first append "assume false" to "b"? (use PathAsideBlock to do this)  --KRML
          builder.Add(ifCmd);
          // Adding the assume stmt, resetting the stmtContext
          stmtContext = StmtType.ASSUME;
          adjustFuelForExists = true;
          builder.Add(TrAssumeCmd(stmt.Tok, etran.TrExpr(stmt.Expr)));
          stmtContext = StmtType.NONE;
        }
      } else if (stmt is ExpectStmt) {
        AddComment(builder, stmt, "expect statement");
        var s = (ExpectStmt)stmt;
        stmtContext = StmtType.ASSUME;
        TrStmt_CheckWellformed(s.Expr, builder, locals, etran, false);

        // Need to check the message is well-formed, assuming the expected expression
        // does NOT hold:
        //
        // if Not(TrExpr[[ s.Expr ]]) {
        //  CheckWellformed[[ s.Message ]]
        //  assume false;
        // }
        BoogieStmtListBuilder thnBuilder = new BoogieStmtListBuilder(this);
        TrStmt_CheckWellformed(s.Message, thnBuilder, locals, etran, false);
        thnBuilder.Add(TrAssumeCmd(stmt.Tok, new Bpl.LiteralExpr(stmt.Tok, false), etran.TrAttributes(stmt.Attributes, null)));
        Bpl.StmtList thn = thnBuilder.Collect(s.Tok);
        builder.Add(new Bpl.IfCmd(stmt.Tok, Bpl.Expr.Not(etran.TrExpr(s.Expr)), thn, null, null));

        stmtContext = StmtType.NONE; // done with translating expect stmt.
      } else if (stmt is AssumeStmt) {
        AddComment(builder, stmt, "assume statement");
        var s = (AssumeStmt)stmt;
        stmtContext = StmtType.ASSUME;
        TrStmt_CheckWellformed(s.Expr, builder, locals, etran, false);
        builder.Add(TrAssumeCmd(stmt.Tok, etran.TrExpr(s.Expr), etran.TrAttributes(stmt.Attributes, null)));
        stmtContext = StmtType.NONE; // done with translating assume stmt.
      }
      this.fuelContext = FuelSetting.PopFuelContext();
    }

    private void TrCalcStmt(CalcStmt stmt, BoogieStmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran) {
      Contract.Requires(stmt != null);
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);

      /* Translate into:
        if (*) {
            assert wf(line0);
        } else if (*) {
            assume wf(line0);
            // if op is ==>: assume line0;
            hint0;
            assert wf(line1);
            assert line0 op line1;
            assume false;
        } else if (*) { ...
        } else if (*) {
            assume wf(line<n-1>);
            // if op is ==>: assume line<n-1>;
            hint<n-1>;
            assert wf(line<n>);
            assert line<n-1> op line<n>;
            assume false;
        }
        assume line<0> op line<n>;
        */
      Contract.Assert(stmt.Steps.Count == stmt.Hints.Count); // established by the resolver
      AddComment(builder, stmt, "calc statement");
      this.fuelContext = FuelSetting.ExpandFuelContext(stmt.Attributes, stmt.Tok, this.fuelContext, this.reporter);
      DefineFuelConstant(stmt.Tok, stmt.Attributes, builder, etran);
      CurrentIdGenerator.Push(); // put the entire calc statement within its own sub-branch
      if (stmt.Lines.Count > 0) {
        Bpl.IfCmd ifCmd = null;
        BoogieStmtListBuilder b;
        // if the dangling hint is empty, do not generate anything for the dummy step
        var stepCount = stmt.Hints.Last().Body.Count == 0 ? stmt.Steps.Count - 1 : stmt.Steps.Count;
        // check steps:
        for (int i = stepCount; 0 <= --i;) {
          b = new BoogieStmtListBuilder(this);
          // assume wf[line<i>]:
          AddComment(b, stmt, "assume wf[lhs]");
          CurrentIdGenerator.Push();
          assertAsAssume = true;
          TrStmt_CheckWellformed(CalcStmt.Lhs(stmt.Steps[i]), b, locals, etran, false);
          assertAsAssume = false;
          if (stmt.Steps[i] is BinaryExpr && (((BinaryExpr)stmt.Steps[i]).ResolvedOp == BinaryExpr.ResolvedOpcode.Imp)) {
            // assume line<i>:
            AddComment(b, stmt, "assume lhs");
            b.Add(TrAssumeCmd(stmt.Tok, etran.TrExpr(CalcStmt.Lhs(stmt.Steps[i]))));
          }
          // hint:
          AddComment(b, stmt, "Hint" + i.ToString());
          TrStmt(stmt.Hints[i], b, locals, etran);
          if (i < stmt.Steps.Count - 1) {
            // non-dummy step
            // check well formedness of the goal line:
            AddComment(b, stmt, "assert wf[rhs]");
            if (stmt.Steps[i] is TernaryExpr) {
              // check the prefix-equality limit
              var index = ((TernaryExpr)stmt.Steps[i]).E0;
              TrStmt_CheckWellformed(index, b, locals, etran, false);
              if (index.Type.IsNumericBased(Type.NumericPersuasion.Int)) {
                var desc = new PODesc.PrefixEqualityLimit();
                b.Add(AssertNS(index.tok, Bpl.Expr.Le(Bpl.Expr.Literal(0), etran.TrExpr(index)), desc));
              }
            }
            TrStmt_CheckWellformed(CalcStmt.Rhs(stmt.Steps[i]), b, locals, etran, false);
            bool splitHappened;
            var ss = TrSplitExpr(stmt.Steps[i], etran, true, out splitHappened);
            // assert step:
            AddComment(b, stmt, "assert line" + i.ToString() + " " + (stmt.StepOps[i] ?? stmt.Op).ToString() + " line" + (i + 1).ToString());
            if (!splitHappened) {
              b.Add(AssertNS(stmt.Lines[i + 1].tok, etran.TrExpr(stmt.Steps[i]), new PODesc.CalculationStep()));
            } else {
              foreach (var split in ss) {
                if (split.IsChecked) {
                  b.Add(AssertNS(stmt.Lines[i + 1].tok, split.E, new PODesc.CalculationStep()));
                }
              }
            }
          }
          b.Add(TrAssumeCmd(stmt.Tok, Bpl.Expr.False));
          ifCmd = new Bpl.IfCmd(stmt.Tok, null, b.Collect(stmt.Tok), ifCmd, null);
          CurrentIdGenerator.Pop();
        }
        // check well formedness of the first line:
        b = new BoogieStmtListBuilder(this);
        AddComment(b, stmt, "assert wf[initial]");
        Contract.Assert(stmt.Result != null); // established by the resolver
        TrStmt_CheckWellformed(CalcStmt.Lhs(stmt.Result), b, locals, etran, false);
        b.Add(TrAssumeCmd(stmt.Tok, Bpl.Expr.False));
        ifCmd = new Bpl.IfCmd(stmt.Tok, null, b.Collect(stmt.Tok), ifCmd, null);
        builder.Add(ifCmd);
        // assume result:
        if (stmt.Steps.Count > 1) {
          builder.Add(TrAssumeCmd(stmt.Tok, etran.TrExpr(stmt.Result)));
        }
      }
      CurrentIdGenerator.Pop();
      this.fuelContext = FuelSetting.PopFuelContext();
    }

    private void TrMatchStmt(MatchStmt stmt, BoogieStmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran) {
      Contract.Requires(stmt != null);
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);

      TrStmt_CheckWellformed(stmt.Source, builder, locals, etran, true);
      Bpl.Expr source = etran.TrExpr(stmt.Source);
      var b = new BoogieStmtListBuilder(this);
      b.Add(TrAssumeCmd(stmt.Tok, Bpl.Expr.False));
      Bpl.StmtList els = b.Collect(stmt.Tok);
      Bpl.IfCmd ifCmd = null;
      foreach (var missingCtor in stmt.MissingCases) {
        // havoc all bound variables
        b = new BoogieStmtListBuilder(this);
        List<Variable> newLocals = new List<Variable>();
        Bpl.Expr r = CtorInvocation(stmt.Tok, missingCtor, etran, newLocals, b);
        locals.AddRange(newLocals);

        if (newLocals.Count != 0) {
          List<Bpl.IdentifierExpr> havocIds = new List<Bpl.IdentifierExpr>();
          foreach (Variable local in newLocals) {
            havocIds.Add(new Bpl.IdentifierExpr(local.tok, local));
          }
          builder.Add(new Bpl.HavocCmd(stmt.Tok, havocIds));
        }
        String missingStr = stmt.Context.FillHole(new IdCtx(missingCtor)).AbstractAllHoles()
          .ToString();
        var desc = new PODesc.MatchIsComplete("statement", missingStr);
        b.Add(Assert(stmt.Tok, Bpl.Expr.False, desc));

        Bpl.Expr guard = Bpl.Expr.Eq(source, r);
        ifCmd = new Bpl.IfCmd(stmt.Tok, guard, b.Collect(stmt.Tok), ifCmd, els);
        els = null;
      }
      for (int i = stmt.Cases.Count; 0 <= --i;) {
        var mc = (MatchCaseStmt)stmt.Cases[i];
        CurrentIdGenerator.Push();
        // havoc all bound variables
        b = new BoogieStmtListBuilder(this);
        List<Variable> newLocals = new List<Variable>();
        Bpl.Expr r = CtorInvocation(mc, stmt.Source.Type, etran, newLocals, b, stmt.IsGhost ? NOALLOC : ISALLOC);
        locals.AddRange(newLocals);

        if (newLocals.Count != 0) {
          List<Bpl.IdentifierExpr> havocIds = new List<Bpl.IdentifierExpr>();
          foreach (Variable local in newLocals) {
            havocIds.Add(new Bpl.IdentifierExpr(local.tok, local));
          }
          builder.Add(new Bpl.HavocCmd(mc.tok, havocIds));
        }

        // translate the body into b
        var prevDefiniteAssignmentTrackerCount = definiteAssignmentTrackers.Count;
        TrStmtList(mc.Body, b, locals, etran);
        RemoveDefiniteAssignmentTrackers(mc.Body, prevDefiniteAssignmentTrackerCount);

        Bpl.Expr guard = Bpl.Expr.Eq(source, r);
        ifCmd = new Bpl.IfCmd(mc.tok, guard, b.Collect(mc.tok), ifCmd, els);
        els = null;
        CurrentIdGenerator.Pop();
      }
      if (ifCmd != null) {
        builder.Add(ifCmd);
      }
    }

    private void TrForLoop(ForLoopStmt stmt, BoogieStmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran) {
      Contract.Requires(stmt != null);
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);

      AddComment(builder, stmt, "for-loop statement");

      var indexVar = stmt.LoopIndex;
      var indexVarName = indexVar.AssignUniqueName(currentDeclaration.IdGenerator);
      var dIndex = new IdentifierExpr(indexVar.tok, indexVar);
      var bIndexVar = new Bpl.LocalVariable(indexVar.tok, new Bpl.TypedIdent(indexVar.Tok, indexVarName, TrType(indexVar.Type)));
      locals.Add(bIndexVar);
      var bIndex = new Bpl.IdentifierExpr(indexVar.tok, indexVarName);

      var lo = stmt.GoingUp ? stmt.Start : stmt.End;
      var hi = stmt.GoingUp ? stmt.End : stmt.Start;
      Expression dLo = null;
      Expression dHi = null;
      Bpl.IdentifierExpr bLo = null;
      Bpl.IdentifierExpr bHi = null;
      if (lo != null) {
        var name = indexVarName + "#lo";
        var bLoVar = new Bpl.LocalVariable(lo.tok, new Bpl.TypedIdent(lo.tok, name, Bpl.Type.Int));
        locals.Add(bLoVar);
        bLo = new Bpl.IdentifierExpr(lo.tok, name);
        CheckWellformed(lo, new WFOptions(null, false), locals, builder, etran);
        builder.Add(Bpl.Cmd.SimpleAssign(lo.tok, bLo, etran.TrExpr(lo)));
        dLo = new BoogieWrapper(bLo, lo.Type);
      }
      if (hi != null) {
        var name = indexVarName + "#hi";
        var bHiVar = new Bpl.LocalVariable(hi.tok, new Bpl.TypedIdent(hi.tok, name, Bpl.Type.Int));
        locals.Add(bHiVar);
        bHi = new Bpl.IdentifierExpr(hi.tok, name);
        CheckWellformed(hi, new WFOptions(null, false), locals, builder, etran);
        builder.Add(Bpl.Cmd.SimpleAssign(hi.tok, bHi, etran.TrExpr(hi)));
        dHi = new BoogieWrapper(bHi, hi.Type);
      }

      // check lo <= hi
      if (lo != null && hi != null) {
        builder.Add(Assert(lo.tok, Bpl.Expr.Le(bLo, bHi), new PODesc.ForRangeBoundsValid()));
      }
      // check forall x :: lo <= x <= hi ==> Is(x, typ)
      {
        // The check, if needed, is performed like this:
        //   var x: int;
        //   havoc x;
        //   assume lo <= x <= hi;
        //   assert Is(x, typ);
        var tok = indexVar.tok;
        var name = indexVarName + "#x";
        var xVar = new Bpl.LocalVariable(tok, new Bpl.TypedIdent(tok, name, Bpl.Type.Int));
        var x = new Bpl.IdentifierExpr(tok, name);
        var cre = GetSubrangeCheck(x, Type.Int, indexVar.Type, out var desc);
        if (cre != null) {
          locals.Add(xVar);
          builder.Add(new Bpl.HavocCmd(tok, new List<Bpl.IdentifierExpr>() { x }));
          builder.Add(new Bpl.AssumeCmd(tok, ForLoopBounds(x, bLo, bHi)));
          builder.Add(Assert(tok, cre, new PODesc.ForRangeAssignable(desc)));
        }
      }

      // initialize the index variable
      builder.Add(Bpl.Cmd.SimpleAssign(indexVar.tok, bIndex, stmt.GoingUp ? bLo : bHi));

      // build the guard expression
      Expression guard;
      if (lo == null || hi == null) {
        guard = LiteralExpr.CreateBoolLiteral(stmt.Tok, true);
      } else {
        guard = Expression.CreateNot(stmt.Tok, Expression.CreateEq(dIndex, stmt.GoingUp ? dHi : dLo, indexVar.Type));
      }

      // free invariant lo <= i <= hi
      var freeInvariant = ForLoopBounds(bIndex, bLo, bHi);

      BodyTranslator bodyTr = null;
      if (stmt.Body != null) {
        bodyTr = delegate (BoogieStmtListBuilder bld, ExpressionTranslator e) {
          CurrentIdGenerator.Push();
          if (!stmt.GoingUp) {
            bld.Add(Bpl.Cmd.SimpleAssign(stmt.Tok, bIndex, Bpl.Expr.Sub(bIndex, Bpl.Expr.Literal(1))));
          }
          TrStmt(stmt.Body, bld, locals, e);
          InsertContinueTarget(stmt, bld);
          if (stmt.GoingUp) {
            bld.Add(Bpl.Cmd.SimpleAssign(stmt.Tok, bIndex, Bpl.Expr.Add(bIndex, Bpl.Expr.Literal(1))));
          }
          CurrentIdGenerator.Pop();
        };
      }

      TrLoop(stmt, guard, bodyTr, builder, locals, etran, freeInvariant, stmt.Decreases.Expressions.Count != 0);
    }

    private void TrWhileStmt(WhileStmt stmt, BoogieStmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran) {
      Contract.Requires(stmt != null);
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);

      AddComment(builder, stmt, "while statement");
      this.fuelContext = FuelSetting.ExpandFuelContext(stmt.Attributes, stmt.Tok, this.fuelContext, this.reporter);
      DefineFuelConstant(stmt.Tok, stmt.Attributes, builder, etran);
      BodyTranslator bodyTr = null;
      if (stmt.Body != null) {
        bodyTr = delegate (BoogieStmtListBuilder bld, ExpressionTranslator e) {
          CurrentIdGenerator.Push();
          TrStmt(stmt.Body, bld, locals, e);
          InsertContinueTarget(stmt, bld);
          CurrentIdGenerator.Pop();
        };
      }
      TrLoop(stmt, stmt.Guard, bodyTr, builder, locals, etran);
      this.fuelContext = FuelSetting.PopFuelContext();
    }

    private void TrIfStmt(IfStmt stmt, BoogieStmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran) {
      Contract.Requires(stmt != null);
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);

      AddComment(builder, stmt, "if statement");
      Expression guard;
      if (stmt.Guard == null) {
        guard = null;
      } else {
        guard = stmt.IsBindingGuard ? AlphaRename((ExistsExpr)stmt.Guard, "eg$") : stmt.Guard;
        TrStmt_CheckWellformed(guard, builder, locals, etran, true);
      }
      BoogieStmtListBuilder b = new BoogieStmtListBuilder(this);
      if (stmt.IsBindingGuard) {
        CurrentIdGenerator.Push();
        var exists = (ExistsExpr)stmt.Guard; // the original (that is, not alpha-renamed) guard
        IntroduceAndAssignExistentialVars(exists, b, builder, locals, etran, stmt.IsGhost);
        CurrentIdGenerator.Pop();
      }
      CurrentIdGenerator.Push();
      Bpl.StmtList thn = TrStmt2StmtList(b, stmt.Thn, locals, etran);
      CurrentIdGenerator.Pop();
      Bpl.StmtList els;
      Bpl.IfCmd elsIf = null;
      b = new BoogieStmtListBuilder(this);
      if (stmt.IsBindingGuard) {
        b.Add(TrAssumeCmd(guard.tok, Bpl.Expr.Not(etran.TrExpr(guard))));
      }
      if (stmt.Els == null) {
        els = b.Collect(stmt.Tok);
      } else {
        CurrentIdGenerator.Push();
        els = TrStmt2StmtList(b, stmt.Els, locals, etran);
        CurrentIdGenerator.Pop();
        if (els.BigBlocks.Count == 1) {
          Bpl.BigBlock bb = els.BigBlocks[0];
          if (bb.LabelName == null && bb.simpleCmds.Count == 0 && bb.ec is Bpl.IfCmd) {
            elsIf = (Bpl.IfCmd)bb.ec;
            els = null;
          }
        }
      }
      builder.Add(new Bpl.IfCmd(stmt.Tok, guard == null || stmt.IsBindingGuard ? null : etran.TrExpr(guard), thn, elsIf, els));
    }


    void TrForallProof(ForallStmt s, BoogieStmtListBuilder definedness, BoogieStmtListBuilder exporter, List<Variable> locals, ExpressionTranslator etran) {
      // Translate:
      //   forall (x,y | Range(x,y))
      //     ensures Post(x,y);
      //   {
      //     Body;
      //   }
      // as:
      //   if (*) {
      //     var x,y;
      //     havoc x,y;
      //     CheckWellformed( Range );
      //     assume Range(x,y);
      //     CheckWellformed( Post );
      //     Tr( Body );       // include only if there is a Body
      //     assert Post;      // include only if there is a Body
      //     assume false;
      //   } else {
      //     assume (forall x,y :: Range(x,y) ==> Post(x,y));
      //   }

      if (s.BoundVars.Count != 0) {
        // Note, it would be nicer (and arguably more appropriate) to do a SetupBoundVarsAsLocals
        // here (rather than a TrBoundVariables).  However, there is currently no way to apply
        // a substMap to a statement (in particular, to s.Body), so that doesn't work here.
        List<bool> freeOfAlloc = null;
        if (FrugalHeapUseX) {
          freeOfAlloc = ComprehensionExpr.BoundedPool.HasBounds(s.Bounds, ComprehensionExpr.BoundedPool.PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc);
        }
        var bVars = new List<Variable>();
        var typeAntecedent = etran.TrBoundVariables(s.BoundVars, bVars, true, freeOfAlloc);
        locals.AddRange(bVars);
        var havocIds = new List<Bpl.IdentifierExpr>();
        foreach (Bpl.Variable bv in bVars) {
          havocIds.Add(new Bpl.IdentifierExpr(s.Tok, bv));
        }
        definedness.Add(new Bpl.HavocCmd(s.Tok, havocIds));
        definedness.Add(TrAssumeCmd(s.Tok, typeAntecedent));
      }
      TrStmt_CheckWellformed(s.Range, definedness, locals, etran, false);
      definedness.Add(TrAssumeCmd(s.Range.tok, etran.TrExpr(s.Range)));

      var ensuresDefinedness = new BoogieStmtListBuilder(this);
      foreach (var ens in s.Ens) {
        TrStmt_CheckWellformed(ens.E, ensuresDefinedness, locals, etran, false);
        ensuresDefinedness.Add(TrAssumeCmd(ens.E.tok, etran.TrExpr(ens.E)));
      }
      PathAsideBlock(s.Tok, ensuresDefinedness, definedness);

      if (s.Body != null) {
        TrStmt(s.Body, definedness, locals, etran);

        // check that postconditions hold
        foreach (var ens in s.Ens) {
          bool splitHappened;  // we actually don't care
          foreach (var split in TrSplitExpr(ens.E, etran, true, out splitHappened)) {
            if (split.IsChecked) {
              definedness.Add(Assert(split.Tok, split.E, new PODesc.ForallPostcondition()));
            }
          }
        }
      }

      definedness.Add(TrAssumeCmd(s.Tok, Bpl.Expr.False));

      // Now for the other branch, where the ensures clauses are exported.
      // If the forall body has side effect such as call to a reveal function,
      // it needs to be exported too.
      var se = s.Body == null ? Bpl.Expr.True : TrFunctionSideEffect(s.Body, etran);
      var substMap = new Dictionary<IVariable, Expression>();
      var p = Substitute(s.ForallExpressions[0], null, substMap);
      var qq = etran.TrExpr(p);
      if (s.BoundVars.Count != 0) {
        exporter.Add(TrAssumeCmd(s.Tok, BplAnd(se, qq)));
      } else {
        exporter.Add(TrAssumeCmd(s.Tok, BplAnd(se, ((Bpl.ForallExpr)qq).Body)));
      }
    }

    /// <summary>
    /// "lhs" is expected to be a resolved form of an expression, i.e., not a concrete-syntax expression.
    /// </summary>
    void TrAssignment(Statement stmt, Expression lhs, AssignmentRhs rhs,
      BoogieStmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran) {
      Contract.Requires(stmt != null);
      Contract.Requires(lhs != null);
      Contract.Requires(!(lhs is ConcreteSyntaxExpression));
      Contract.Requires(!(lhs is SeqSelectExpr && !((SeqSelectExpr)lhs).SelectOne));  // these were once allowed, but their functionality is now provided by 'forall' statements
      Contract.Requires(rhs != null);
      Contract.Requires(builder != null);
      Contract.Requires(cce.NonNullElements(locals));
      Contract.Requires(etran != null);
      Contract.Requires(predef != null);

      List<AssignToLhs> lhsBuilder;
      List<Bpl.IdentifierExpr> bLhss;
      var lhss = new List<Expression>() { lhs };
      Bpl.Expr[] ignore1, ignore2;
      string[] ignore3;
      ProcessLhss(lhss, rhs.CanAffectPreviouslyKnownExpressions, true, builder, locals, etran,
        out lhsBuilder, out bLhss, out ignore1, out ignore2, out ignore3);
      Contract.Assert(lhsBuilder.Count == 1 && bLhss.Count == 1);  // guaranteed by postcondition of ProcessLhss

      var rhss = new List<AssignmentRhs>() { rhs };
      ProcessRhss(lhsBuilder, bLhss, lhss, rhss, builder, locals, etran);
      builder.AddCaptureState(stmt);
    }

    void TrForallAssign(ForallStmt s, AssignStmt s0,
      BoogieStmtListBuilder definedness, BoogieStmtListBuilder updater, List<Variable> locals, ExpressionTranslator etran) {
      // The statement:
      //   forall (x,y | Range(x,y)) {
      //     (a)   E(x,y) . f :=  G(x,y);
      //     (b)   A(x,y) [ I0(x,y), I1(x,y), ... ] :=  G(x,y);
      //   }
      // translate into:
      //   if (*) {
      //     // check definedness of Range
      //     var x,y;
      //     havoc x,y;
      //     CheckWellformed( Range );
      //     assume Range;
      //     // check definedness of the other expressions
      //     (a)
      //       CheckWellformed( E.F );
      //       check that E.f is in the modifies frame;
      //       CheckWellformed( G );
      //       check nat restrictions for the RHS
      //     (b)
      //       CheckWellformed( A[I0,I1,...] );
      //       check that A[I0,I1,...] is in the modifies frame;
      //       CheckWellformed( G );
      //       check nat restrictions for the RHS
      //     // check for duplicate LHSs
      //     var x', y';
      //     havoc x', y';
      //     assume Range[x,y := x',y'];
      //     assume !(x == x' && y == y');
      //     (a)
      //       assert E(x,y) != E(x',y') || G(x,y) == G(x',y');
      //     (b)
      //       assert !( A(x,y)==A(x',y') && I0(x,y)==I0(x',y') && I1(x,y)==I1(x',y') && ... ) || G(x,y) == G(x',y');
      //
      //     assume false;
      //
      //   } else {
      //     var oldHeap := $Heap;
      //     havoc $Heap;
      //     assume $HeapSucc(oldHeap, $Heap);
      //     (a)
      //       assume (forall<alpha> o: ref, F: Field alpha ::
      //         { $Heap[o,F] }
      //         $Heap[o,F] = oldHeap[o,F] ||
      //         (exists x,y :: Range(x,y) && o == E(x,y) && F = f));
      //       assume (forall x,y ::  Range ==> $Heap[ E[$Heap:=oldHeap], F] == G[$Heap:=oldHeap]); (**)
      //     (b)
      //       assume (forall<alpha> o: ref, F: Field alpha ::
      //         { $Heap[o,F] }
      //         $Heap[o,F] = oldHeap[o,F] ||
      //         (exists x,y :: Range(x,y) && o == A(x,y) && F = Index(I0,I1,...)));
      //       assume (forall x,y ::  Range ==> $Heap[ A[$Heap:=oldHeap], Index(I0,I1,...)] == G[$Heap:=oldHeap]); (**)
      //   }
      //
      // Note: In order to get a good trigger for the quantifiers (**), we will attempt to make the parameters
      // that select from $Heap in the LHS of the equalities as plain as possible.  This involves taking the inverse
      // of an expression, which isn't always easy or possible, so we settle for handling some common cases.  In
      // particular, we change:
      //   0: forall i | R(i) { F(i).f := E(i); }
      //   1: forall i | R(i) { A[F(i)] := E(i); }
      //   2: forall i | R(i) { F(i)[N] := E(i); }
      // where f is some field and A and N are expressions that do not depend on i, into:
      //   0: forall j | Q(j) { j.f := E(F-1(j)); }
      //   1: forall j | Q(j) { A[j] := E(F-1(j)); }
      //   2: forall j | Q(j) { j[N] := E(F-1(j)); }
      // where we ensure that, for all i and j:
      //   R(i) && j == F(i)    <==>    Q(j) && F-1(j) == i
      // If the transformation succeeds, we use, respectively, j.f, A[j], and j[N] (each evaluated in the new heap) as
      // the trigger of the quantifier generated.

      var substMap = SetupBoundVarsAsLocals(s.BoundVars, definedness, locals, etran);
      Expression range = Substitute(s.Range, null, substMap);
      TrStmt_CheckWellformed(range, definedness, locals, etran, false);
      definedness.Add(TrAssumeCmd(s.Range.tok, etran.TrExpr(range)));

      var lhs = Substitute(s0.Lhs.Resolved, null, substMap);
      TrStmt_CheckWellformed(lhs, definedness, locals, etran, false);
      Bpl.Expr obj, F;
      string description = GetObjFieldDetails(lhs, etran, out obj, out F);
      definedness.Add(Assert(lhs.tok, Bpl.Expr.SelectTok(lhs.tok, etran.TheFrame(lhs.tok), obj, F),
        new PODesc.Modifiable(description)));
      if (s0.Rhs is ExprRhs) {
        var r = (ExprRhs)s0.Rhs;
        var rhs = Substitute(r.Expr, null, substMap);
        TrStmt_CheckWellformed(rhs, definedness, locals, etran, false);
        // check nat restrictions for the RHS
        Type lhsType;
        if (lhs is MemberSelectExpr) {
          lhsType = ((MemberSelectExpr)lhs).Type;
        } else if (lhs is SeqSelectExpr) {
          lhsType = ((SeqSelectExpr)lhs).Type;
        } else {
          lhsType = ((MultiSelectExpr)lhs).Type;
        }
        var translatedRhs = etran.TrExpr(rhs);
        CheckSubrange(r.Tok, translatedRhs, rhs.Type, lhsType, definedness);
        if (lhs is MemberSelectExpr) {
          var fse = (MemberSelectExpr)lhs;
          var field = fse.Member as Field;
          Contract.Assert(field != null);
          Check_NewRestrictions(fse.tok, obj, field, translatedRhs, definedness, etran);
        }
      }

      // check for duplicate LHSs
      if (s0.Rhs is ExprRhs) {  // if Rhs denotes a havoc, then no duplicate check is performed
        var substMapPrime = SetupBoundVarsAsLocals(s.BoundVars, definedness, locals, etran);
        var lhsPrime = Substitute(s0.Lhs.Resolved, null, substMapPrime);
        range = Substitute(s.Range, null, substMapPrime);
        definedness.Add(TrAssumeCmd(range.tok, etran.TrExpr(range)));
        // assume !(x == x' && y == y');
        Bpl.Expr eqs = Bpl.Expr.True;
        foreach (var bv in s.BoundVars) {
          var x = substMap[bv];
          var xPrime = substMapPrime[bv];
          // TODO: in the following line, is the term equality okay, or does it have to include things like Set#Equal sometimes too?
          eqs = BplAnd(eqs, Bpl.Expr.Eq(etran.TrExpr(x), etran.TrExpr(xPrime)));
        }
        definedness.Add(TrAssumeCmd(s.Tok, Bpl.Expr.Not(eqs)));
        Bpl.Expr objPrime, FPrime;
        GetObjFieldDetails(lhsPrime, etran, out objPrime, out FPrime);
        var Rhs = ((ExprRhs)s0.Rhs).Expr;
        var rhs = etran.TrExpr(Substitute(Rhs, null, substMap));
        var rhsPrime = etran.TrExpr(Substitute(Rhs, null, substMapPrime));
        definedness.Add(Assert(s0.Tok,
          Bpl.Expr.Or(
            Bpl.Expr.Or(Bpl.Expr.Neq(obj, objPrime), Bpl.Expr.Neq(F, FPrime)),
            Bpl.Expr.Eq(rhs, rhsPrime)),
          new PODesc.ForallLHSUnique()));
      }

      definedness.Add(TrAssumeCmd(s.Tok, Bpl.Expr.False));

      // Now for the translation of the update itself

      Bpl.IdentifierExpr prevHeap = GetPrevHeapVar_IdExpr(s.Tok, locals);
      var prevEtran = new ExpressionTranslator(this, predef, prevHeap);
      updater.Add(Bpl.Cmd.SimpleAssign(s.Tok, prevHeap, etran.HeapExpr));
      updater.Add(new Bpl.HavocCmd(s.Tok, new List<Bpl.IdentifierExpr> { etran.HeapCastToIdentifierExpr }));
      updater.Add(TrAssumeCmd(s.Tok, HeapSucc(prevHeap, etran.HeapExpr)));

      // Here comes:
      //   assume (forall<alpha> o: ref, f: Field alpha ::
      //     { $Heap[o,f] }
      //     $Heap[o,f] = oldHeap[o,f] ||
      //     (exists x,y :: Range(x,y)[$Heap:=oldHeap] &&
      //                    o == Object(x,y)[$Heap:=oldHeap] && f == Field(x,y)[$Heap:=oldHeap]));
      Bpl.TypeVariable alpha = new Bpl.TypeVariable(s.Tok, "alpha");
      Bpl.BoundVariable oVar = new Bpl.BoundVariable(s.Tok, new Bpl.TypedIdent(s.Tok, "$o", predef.RefType));
      Bpl.IdentifierExpr o = new Bpl.IdentifierExpr(s.Tok, oVar);
      Bpl.BoundVariable fVar = new Bpl.BoundVariable(s.Tok, new Bpl.TypedIdent(s.Tok, "$f", predef.FieldName(s.Tok, alpha)));
      Bpl.IdentifierExpr f = new Bpl.IdentifierExpr(s.Tok, fVar);
      Bpl.Expr heapOF = ExpressionTranslator.ReadHeap(s.Tok, etran.HeapExpr, o, f);
      Bpl.Expr oldHeapOF = ExpressionTranslator.ReadHeap(s.Tok, prevHeap, o, f);
      List<bool> freeOfAlloc = null;
      if (FrugalHeapUseX) {
        freeOfAlloc = ComprehensionExpr.BoundedPool.HasBounds(s.Bounds, ComprehensionExpr.BoundedPool.PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc);
      }
      List<Variable> xBvars = new List<Variable>();
      var xBody = etran.TrBoundVariables(s.BoundVars, xBvars, false, freeOfAlloc);
      xBody = BplAnd(xBody, prevEtran.TrExpr(s.Range));
      Bpl.Expr xObj, xField;
      GetObjFieldDetails(s0.Lhs.Resolved, prevEtran, out xObj, out xField);
      xBody = BplAnd(xBody, Bpl.Expr.Eq(o, xObj));
      xBody = BplAnd(xBody, Bpl.Expr.Eq(f, xField));
      //TRIG (exists k#2: int :: (k#2 == LitInt(0 - 3) || k#2 == LitInt(4)) && $o == read($prevHeap, this, _module.MyClass.arr) && $f == MultiIndexField(IndexField(i#0), j#0))
      Bpl.Expr xObjField = new Bpl.ExistsExpr(s.Tok, xBvars, xBody);  // LL_TRIGGER
      Bpl.Expr body = Bpl.Expr.Or(Bpl.Expr.Eq(heapOF, oldHeapOF), xObjField);
      var tr = new Trigger(s.Tok, true, new List<Expr>() { heapOF });
      Bpl.Expr qq = new Bpl.ForallExpr(s.Tok, new List<TypeVariable> { alpha }, new List<Variable> { oVar, fVar }, null, tr, body);
      updater.Add(TrAssumeCmd(s.Tok, qq));

      if (s.ForallExpressions != null) {
        foreach (ForallExpr expr in s.ForallExpressions) {
          BinaryExpr term = (BinaryExpr)expr.Term;
          Contract.Assert(term != null);
          var e0 = ((BinaryExpr)term).E0.Resolved;
          var e1 = ((BinaryExpr)term).E1;
          qq = TrForall_NewValueAssumption(expr.tok, expr.BoundVars, expr.Bounds, expr.Range, e0, e1, expr.Attributes, etran, prevEtran);
          updater.Add(TrAssumeCmd(s.Tok, qq));
        }
      }
    }

    /// <summary>
    /// Generate:
    ///   assume (forall x,y :: Range(x,y)[$Heap:=oldHeap] ==>
    ///                         $Heap[ Object(x,y)[$Heap:=oldHeap], Field(x,y)[$Heap:=oldHeap] ] == G[$Heap:=oldHeap] ));
    /// where
    ///   x,y           represent boundVars
    ///   Object(x,y)   is the first part of lhs
    ///   Field(x,y)    is the second part of lhs
    ///   G             is rhs
    /// If lhsAsTrigger is true, then use the LHS of the equality above as the trigger; otherwise, don't specify any trigger.
    /// </summary>
    private Bpl.Expr TrForall_NewValueAssumption(IToken tok, List<BoundVar> boundVars, List<ComprehensionExpr.BoundedPool> bounds, Expression range, Expression lhs, Expression rhs, Attributes attributes, ExpressionTranslator etran, ExpressionTranslator prevEtran) {
      Contract.Requires(tok != null);
      Contract.Requires(boundVars != null);
      Contract.Requires(!FrugalHeapUseX || bounds != null);
      Contract.Requires(range != null);
      Contract.Requires(lhs != null);
      Contract.Requires(rhs != null);
      Contract.Requires(etran != null);
      Contract.Requires(prevEtran != null);

      List<bool> freeOfAlloc = null;
      if (FrugalHeapUseX) {
        freeOfAlloc = ComprehensionExpr.BoundedPool.HasBounds(bounds, ComprehensionExpr.BoundedPool.PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc);
      }
      var xBvars = new List<Variable>();
      Bpl.Expr xAnte = etran.TrBoundVariables(boundVars, xBvars, false, freeOfAlloc);
      xAnte = BplAnd(xAnte, prevEtran.TrExpr(range));
      var g = prevEtran.TrExpr(rhs);
      Bpl.Expr obj, field;
      GetObjFieldDetails(lhs, prevEtran, out obj, out field);
      var xHeapOF = ExpressionTranslator.ReadHeap(tok, etran.HeapExpr, obj, field);

      Type lhsType = lhs is MemberSelectExpr ? ((MemberSelectExpr)lhs).Type : null;
      g = CondApplyBox(rhs.tok, g, rhs.Type, lhsType);

      Bpl.Trigger tr = null;
      var argsEtran = etran.WithNoLits();
      foreach (var aa in attributes.AsEnumerable()) {
        if (aa.Name == "trigger") {
          List<Bpl.Expr> tt = new List<Bpl.Expr>();
          foreach (var arg in aa.Args) {
            if (arg == lhs) {
              tt.Add(xHeapOF);
            } else {
              tt.Add(argsEtran.TrExpr(arg));
            }
          }
          tr = new Bpl.Trigger(tok, true, tt, tr);
        }
      }
      return new Bpl.ForallExpr(tok, xBvars, tr, Bpl.Expr.Imp(xAnte, Bpl.Expr.Eq(xHeapOF, g)));
    }

    void TrLoop(LoopStmt s, Expression Guard, BodyTranslator/*?*/ bodyTr,
                BoogieStmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran,
                Bpl.Expr freeInvariant = null, bool includeTerminationCheck = true) {
      Contract.Requires(s != null);
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);

      var suffix = CurrentIdGenerator.FreshId("loop#");

      var theDecreases = s.Decreases.Expressions;

      Bpl.LocalVariable preLoopHeapVar = new Bpl.LocalVariable(s.Tok, new Bpl.TypedIdent(s.Tok, "$PreLoopHeap$" + suffix, predef.HeapType));
      locals.Add(preLoopHeapVar);
      Bpl.IdentifierExpr preLoopHeap = new Bpl.IdentifierExpr(s.Tok, preLoopHeapVar);
      ExpressionTranslator etranPreLoop = new ExpressionTranslator(this, predef, preLoopHeap);
      ExpressionTranslator updatedFrameEtran;
      string loopFrameName = "$Frame$" + suffix;
      if (s.Mod.Expressions != null) {
        updatedFrameEtran = new ExpressionTranslator(etran, loopFrameName);
      } else {
        updatedFrameEtran = etran;
      }

      if (s.Mod.Expressions != null) { // check well-formedness and that the modifies is a subset
        CheckFrameWellFormed(new WFOptions(), s.Mod.Expressions, locals, builder, etran);
        CheckFrameSubset(s.Tok, s.Mod.Expressions, null, null, etran, builder, new PODesc.FrameSubset("loop modifies clause", true), null);
        DefineFrame(s.Tok, s.Mod.Expressions, builder, locals, loopFrameName);
      }
      builder.Add(Bpl.Cmd.SimpleAssign(s.Tok, preLoopHeap, etran.HeapExpr));

      var daTrackersMonotonicity = new List<Tuple<Bpl.IdentifierExpr, Bpl.IdentifierExpr>>();
      foreach (var dat in definiteAssignmentTrackers.Values) {  // TODO: the order is non-deterministic and may change between invocations of Dafny
        var preLoopDat = new Bpl.LocalVariable(dat.tok, new Bpl.TypedIdent(dat.tok, "preLoop$" + suffix + "$" + dat.Name, dat.Type));
        locals.Add(preLoopDat);
        var ie = new Bpl.IdentifierExpr(s.Tok, preLoopDat);
        daTrackersMonotonicity.Add(new Tuple<Bpl.IdentifierExpr, Bpl.IdentifierExpr>(ie, dat));
        builder.Add(Bpl.Cmd.SimpleAssign(s.Tok, ie, dat));
      }

      List<Bpl.Expr> initDecr = null;
      if (!Contract.Exists(theDecreases, e => e is WildcardExpr)) {
        initDecr = RecordDecreasesValue(theDecreases, builder, locals, etran, "$decr_init$" + suffix);
      }

      // The variable w is used to coordinate the definedness checking of the loop invariant.
      // It is also used for body-less loops to turn off invariant checking after the generated body.
      Bpl.LocalVariable wVar = new Bpl.LocalVariable(s.Tok, new Bpl.TypedIdent(s.Tok, "$w$" + suffix, Bpl.Type.Bool));
      Bpl.IdentifierExpr w = new Bpl.IdentifierExpr(s.Tok, wVar);
      locals.Add(wVar);
      // havoc w;
      builder.Add(new Bpl.HavocCmd(s.Tok, new List<Bpl.IdentifierExpr> { w }));

      List<Bpl.PredicateCmd> invariants = new List<Bpl.PredicateCmd>();
      if (freeInvariant != null) {
        invariants.Add(new Bpl.AssumeCmd(freeInvariant.tok, freeInvariant));
      }
      BoogieStmtListBuilder invDefinednessBuilder = new BoogieStmtListBuilder(this);
      foreach (AttributedExpression loopInv in s.Invariants) {
        string errorMessage = CustomErrorMessage(loopInv.Attributes);
        TrStmt_CheckWellformed(loopInv.E, invDefinednessBuilder, locals, etran, false);
        invDefinednessBuilder.Add(TrAssumeCmd(loopInv.E.tok, etran.TrExpr(loopInv.E)));

        invariants.Add(TrAssumeCmd(loopInv.E.tok, Bpl.Expr.Imp(w, CanCallAssumption(loopInv.E, etran))));
        bool splitHappened;
        var ss = TrSplitExpr(loopInv.E, etran, false, out splitHappened);
        if (!splitHappened) {
          var wInv = Bpl.Expr.Imp(w, etran.TrExpr(loopInv.E));
          invariants.Add(Assert(loopInv.E.tok, wInv, new PODesc.LoopInvariant(errorMessage)));
        } else {
          foreach (var split in ss) {
            var wInv = Bpl.Expr.Binary(split.E.tok, BinaryOperator.Opcode.Imp, w, split.E);
            if (split.IsChecked) {
              invariants.Add(Assert(split.Tok, wInv, new PODesc.LoopInvariant(errorMessage)));  // TODO: it would be fine to have this use {:subsumption 0}
            } else {
              invariants.Add(TrAssumeCmd(split.E.tok, wInv));
            }
          }
        }
      }
      // check definedness of decreases clause
      foreach (Expression e in theDecreases) {
        TrStmt_CheckWellformed(e, invDefinednessBuilder, locals, etran, true);
      }
      if (codeContext is IMethodCodeContext) {
        var modifiesClause = ((IMethodCodeContext)codeContext).Modifies.Expressions;
        if (codeContext is IteratorDecl) {
          // add "this" to the explicit modifies clause
          var explicitModifies = modifiesClause;
          modifiesClause = new List<FrameExpression>();
          modifiesClause.Add(new FrameExpression(s.Tok, new ThisExpr((IteratorDecl)codeContext), null));
          modifiesClause.AddRange(explicitModifies);
        }
        // include boilerplate invariants
        foreach (BoilerplateTriple tri in GetTwoStateBoilerplate(s.Tok, modifiesClause, s.IsGhost, codeContext.AllowsAllocation, etranPreLoop, etran, etran.Old)) {
          if (tri.IsFree) {
            invariants.Add(TrAssumeCmd(s.Tok, tri.Expr));
          } else {
            Contract.Assert(tri.ErrorMessage != null);  // follows from BoilerplateTriple invariant
            invariants.Add(Assert(s.Tok, tri.Expr, new PODesc.BoilerplateTriple(tri.ErrorMessage)));
          }
        }
        // add a free invariant which says that the heap hasn't changed outside of the modifies clause.
        invariants.Add(TrAssumeCmd(s.Tok, FrameConditionUsingDefinedFrame(s.Tok, etranPreLoop, etran, updatedFrameEtran)));
        // for iterators, add "fresh(_new)" as an invariant
        if (codeContext is IteratorDecl iter) {
          var th = new ThisExpr(iter);
          var thisDotNew = new MemberSelectExpr(s.Tok, th, iter.Member_New);
          var fr = new FreshExpr(s.Tok, thisDotNew);
          fr.Type = Type.Bool;
          invariants.Add(TrAssertCmd(s.Tok, etran.TrExpr(fr)));
        }
      }

      // include a free invariant that says that all definite-assignment trackers have only become more "true"
      foreach (var pair in daTrackersMonotonicity) {
        Bpl.Expr monotonic = Bpl.Expr.Imp(pair.Item1, pair.Item2);
        invariants.Add(TrAssumeCmd(s.Tok, monotonic));
      }

      // include a free invariant that says that all completed iterations so far have only decreased the termination metric
      if (initDecr != null) {
        var toks = new List<IToken>();
        var types = new List<Type>();
        var decrs = new List<Expr>();
        foreach (Expression e in theDecreases) {
          toks.Add(e.tok);
          types.Add(e.Type.NormalizeExpand());
          decrs.Add(etran.TrExpr(e));
        }
        Bpl.Expr decrCheck = DecreasesCheck(toks, types, types, decrs, initDecr, null, null, true, false);
        invariants.Add(TrAssumeCmd(s.Tok, decrCheck));
      }

      var loopBodyBuilder = new BoogieStmtListBuilder(this);
      loopBodyBuilder.AddCaptureState(s.Tok, true, "after some loop iterations");

      // As the first thing inside the loop, generate:  if (!w) { CheckWellformed(inv); assume false; }
      invDefinednessBuilder.Add(TrAssumeCmd(s.Tok, Bpl.Expr.False));
      loopBodyBuilder.Add(new Bpl.IfCmd(s.Tok, Bpl.Expr.Not(w), invDefinednessBuilder.Collect(s.Tok), null, null));

      // Generate:  CheckWellformed(guard); if (!guard) { break; }
      // but if this is a body-less loop, put all of that inside:  if (*) { ... }
      // Without this, Boogie's abstract interpreter may figure out that the loop guard is always false
      // on entry to the loop, and then Boogie wouldn't consider this a loop at all. (See also comment
      // in methods GuardAlwaysHoldsOnEntry_BodyLessLoop and GuardAlwaysHoldsOnEntry_LoopWithBody in
      // Test/dafny0/DirtyLoops.dfy.)
      var isBodyLessLoop = s is OneBodyLoopStmt && ((OneBodyLoopStmt)s).BodySurrogate != null;
      var whereToBuildLoopGuard = isBodyLessLoop ? new BoogieStmtListBuilder(this) : loopBodyBuilder;
      Bpl.Expr guard = null;
      if (Guard != null) {
        TrStmt_CheckWellformed(Guard, whereToBuildLoopGuard, locals, etran, true);
        guard = Bpl.Expr.Not(etran.TrExpr(Guard));
      }
      var guardBreak = new BoogieStmtListBuilder(this);
      guardBreak.Add(new Bpl.BreakCmd(s.Tok, null));
      whereToBuildLoopGuard.Add(new Bpl.IfCmd(s.Tok, guard, guardBreak.Collect(s.Tok), null, null));
      if (isBodyLessLoop) {
        loopBodyBuilder.Add(new Bpl.IfCmd(s.Tok, null, whereToBuildLoopGuard.Collect(s.Tok), null, null));
      }

      if (bodyTr != null) {
        // termination checking
        if (Contract.Exists(theDecreases, e => e is WildcardExpr)) {
          // omit termination checking for this loop
          bodyTr(loopBodyBuilder, updatedFrameEtran);
        } else {
          List<Bpl.Expr> oldBfs = RecordDecreasesValue(theDecreases, loopBodyBuilder, locals, etran, "$decr$" + suffix);
          // time for the actual loop body
          bodyTr(loopBodyBuilder, updatedFrameEtran);
          // check definedness of decreases expressions
          var toks = new List<IToken>();
          var types = new List<Type>();
          var decrs = new List<Expr>();
          foreach (Expression e in theDecreases) {
            toks.Add(e.tok);
            types.Add(e.Type.NormalizeExpand());
            decrs.Add(etran.TrExpr(e));
          }
          if (includeTerminationCheck) {
            AddComment(loopBodyBuilder, s, "loop termination check");
            Bpl.Expr decrCheck = DecreasesCheck(toks, types, types, decrs, oldBfs, loopBodyBuilder, " at end of loop iteration", false, false);
            loopBodyBuilder.Add(Assert(s.Tok, decrCheck, new PODesc.Terminates(s.InferredDecreases, true)));
          }
        }
      } else if (isBodyLessLoop) {
        var bodySurrogate = ((OneBodyLoopStmt)s).BodySurrogate;
        // This is a body-less loop. Havoc the targets and then set w to false, to make the loop-invariant
        // maintenance check vaccuous.
        var bplTargets = bodySurrogate.LocalLoopTargets.ConvertAll(v => TrVar(s.Tok, v));
        if (bodySurrogate.UsesHeap) {
          bplTargets.Add(etran.HeapCastToIdentifierExpr);
        }
        loopBodyBuilder.Add(new Bpl.HavocCmd(s.Tok, bplTargets));
        loopBodyBuilder.Add(Bpl.Cmd.SimpleAssign(s.Tok, w, Bpl.Expr.False));
      }
      // Finally, assume the well-formedness of the invariant (which has been checked once and for all above), so that the check
      // of invariant-maintenance can use the appropriate canCall predicates. Note, it is important (see Test/git-issues/git-issue-1812.dfy)
      // that each CanCall assumption uses the preceding invariants as antecedents--this is achieved by treating all "invariant"
      // declarations as one big conjunction, because then CanCallAssumption will add the needed antecedents.
      if (s.Invariants.Any()) {
        var allInvariants = s.Invariants.Select(inv => inv.E).Aggregate((a, b) => Expression.CreateAnd(a, b));
        loopBodyBuilder.Add(TrAssumeCmd(s.Tok, CanCallAssumption(allInvariants, etran)));
      }

      Bpl.StmtList body = loopBodyBuilder.Collect(s.Tok);
      builder.Add(new Bpl.WhileCmd(s.Tok, Bpl.Expr.True, invariants, body));
    }

    void InsertContinueTarget(LoopStmt loop, BoogieStmtListBuilder builder) {
      Contract.Requires(loop != null);
      Contract.Requires(builder != null);
      if (loop.Labels != null) {
        builder.AddLabelCmd("continue_" + loop.Labels.Data.AssignUniqueId(CurrentIdGenerator));
      }
    }

    void TrAlternatives(List<GuardedAlternative> alternatives, Bpl.Cmd elseCase0, Bpl.StructuredCmd elseCase1,
                        BoogieStmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran, bool isGhost) {
      Contract.Requires(alternatives != null);
      Contract.Requires((elseCase0 == null) != (elseCase1 == null));  // ugly way of doing a type union
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);

      if (alternatives.Count == 0) {
        if (elseCase0 != null) {
          builder.Add(elseCase0);
        } else {
          builder.Add(elseCase1);
        }
        return;
      }

      // alpha-rename any binding guards
      var guards = alternatives.ConvertAll(alt => alt.IsBindingGuard ? AlphaRename((ExistsExpr)alt.Guard, "eg$") : alt.Guard);

      // build the negation of the disjunction of all guards (that is, the conjunction of their negations)
      Bpl.Expr noGuard = Bpl.Expr.True;
      var b = new BoogieStmtListBuilder(this);
      foreach (var g in guards) {
        b.Add(TrAssumeCmd(g.tok, CanCallAssumption(g, etran)));
        noGuard = BplAnd(noGuard, Bpl.Expr.Not(etran.TrExpr(g)));
      }

      var elseTok = elseCase0 != null ? elseCase0.tok : elseCase1.tok;
      b.Add(TrAssumeCmd(elseTok, noGuard));
      if (elseCase0 != null) {
        b.Add(elseCase0);
      } else {
        b.Add(elseCase1);
      }
      Bpl.StmtList els = b.Collect(elseTok);

      Bpl.IfCmd elsIf = null;
      for (int i = alternatives.Count; 0 <= --i;) {
        Contract.Assert(elsIf == null || els == null);  // loop invariant
        CurrentIdGenerator.Push();
        var alternative = alternatives[i];
        b = new BoogieStmtListBuilder(this);
        TrStmt_CheckWellformed(guards[i], b, locals, etran, true);
        if (alternative.IsBindingGuard) {
          var exists = (ExistsExpr)alternative.Guard;  // the original (that is, not alpha-renamed) guard
          IntroduceAndAssignExistentialVars(exists, b, builder, locals, etran, isGhost);
        } else {
          b.Add(new AssumeCmd(alternative.Guard.tok, etran.TrExpr(alternative.Guard)));
        }
        var prevDefiniteAssignmentTrackerCount = definiteAssignmentTrackers.Count;
        TrStmtList(alternative.Body, b, locals, etran);
        RemoveDefiniteAssignmentTrackers(alternative.Body, prevDefiniteAssignmentTrackerCount);
        Bpl.StmtList thn = b.Collect(alternative.Tok);
        elsIf = new Bpl.IfCmd(alternative.Tok, null, thn, elsIf, els);
        els = null;
        CurrentIdGenerator.Pop();
      }
      Contract.Assert(elsIf != null && els == null); // follows from loop invariant and the fact that there's more than one alternative
      builder.Add(elsIf);
    }

    void TrCallStmt(CallStmt s, BoogieStmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran, Bpl.IdentifierExpr actualReceiver) {
      Contract.Requires(s != null);
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);
      Contract.Requires(!(s.Method is Constructor) || (s.Lhs.Count == 0 && actualReceiver != null));

      List<AssignToLhs> lhsBuilders;
      List<Bpl.IdentifierExpr> bLhss;
      var tySubst = s.MethodSelect.TypeArgumentSubstitutionsWithParents();
      ProcessLhss(s.Lhs, true, true, builder, locals, etran, out lhsBuilders, out bLhss,
        out _, out _, out _, s.OriginalInitialLhs);
      Contract.Assert(s.Lhs.Count == lhsBuilders.Count);
      Contract.Assert(s.Lhs.Count == bLhss.Count);
      var lhsTypes = new List<Type>();
      if (s.Method is Constructor) {
        lhsTypes.Add(s.Receiver.Type);
        bLhss.Add(actualReceiver);
      } else {
        for (int i = 0; i < s.Lhs.Count; i++) {
          var lhs = s.Lhs[i];
          lhsTypes.Add(lhs.Type);
          builder.Add(new CommentCmd("TrCallStmt: Adding lhs with type " + lhs.Type));
          if (bLhss[i] == null) {  // (in the current implementation, the second parameter "true" to ProcessLhss implies that all bLhss[*] will be null)
            // create temporary local and assign it to bLhss[i]
            string nm = CurrentIdGenerator.FreshId("$rhs##");
            var formalOutType = s.Method.Outs[i].Type.Subst(tySubst);
            var ty = TrType(formalOutType);
            Bpl.LocalVariable var = new Bpl.LocalVariable(lhs.tok, new Bpl.TypedIdent(lhs.tok, nm, ty));
            locals.Add(var);
            bLhss[i] = new Bpl.IdentifierExpr(lhs.tok, var.Name, ty);
          }
        }
      }
      Bpl.IdentifierExpr initHeap = null;
      if (codeContext is IteratorDecl) {
        // var initHeap := $Heap;
        var initHeapVar = new Bpl.LocalVariable(s.Tok, new Bpl.TypedIdent(s.Tok, CurrentIdGenerator.FreshId("$initHeapCallStmt#"), predef.HeapType));
        locals.Add(initHeapVar);
        initHeap = new Bpl.IdentifierExpr(s.Tok, initHeapVar);
        // initHeap := $Heap;
        builder.Add(Bpl.Cmd.SimpleAssign(s.Tok, initHeap, etran.HeapExpr));
      }
      builder.Add(new CommentCmd("TrCallStmt: Before ProcessCallStmt"));
      ProcessCallStmt(GetToken(s), tySubst, GetTypeParams(s.Method), s.Receiver, actualReceiver, s.Method, s.MethodSelect.AtLabel, s.Args, bLhss, lhsTypes, builder, locals, etran);
      builder.Add(new CommentCmd("TrCallStmt: After ProcessCallStmt"));
      for (int i = 0; i < lhsBuilders.Count; i++) {
        var lhs = s.Lhs[i];
        Type lhsType, rhsTypeConstraint;
        if (lhs is IdentifierExpr) {
          var ide = (IdentifierExpr)lhs;
          lhsType = ide.Var.Type;
          rhsTypeConstraint = lhsType;
        } else if (lhs is MemberSelectExpr) {
          var fse = (MemberSelectExpr)lhs;
          var field = (Field)fse.Member;
          Contract.Assert(field != null);
          Contract.Assert(VisibleInScope(field));
          lhsType = field.Type;
          rhsTypeConstraint = lhsType.Subst(fse.TypeArgumentSubstitutionsWithParents());
        } else if (lhs is SeqSelectExpr) {
          var e = (SeqSelectExpr)lhs;
          lhsType = null;  // for arrays, always make sure the value assigned is boxed
          rhsTypeConstraint = e.Seq.Type.TypeArgs[0];
        } else {
          var e = (MultiSelectExpr)lhs;
          lhsType = null;  // for arrays, always make sure the value assigned is boxed
          rhsTypeConstraint = e.Array.Type.TypeArgs[0];
        }

        Bpl.Expr bRhs = bLhss[i];  // the RHS (bRhs) of the assignment to the actual call-LHS (lhs) was a LHS (bLhss[i]) in the Boogie call statement
        CheckSubrange(lhs.tok, bRhs, s.Method.Outs[i].Type.Subst(tySubst), rhsTypeConstraint, builder);
        bRhs = CondApplyBox(lhs.tok, bRhs, lhs.Type, lhsType);

        lhsBuilders[i](bRhs, false, builder, etran);
      }
      if (codeContext is IteratorDecl) {
        var iter = (IteratorDecl)codeContext;
        Contract.Assert(initHeap != null);
        RecordNewObjectsIn_New(s.Tok, iter, initHeap, etran.HeapCastToIdentifierExpr, builder, locals, etran);
      }
      builder.AddCaptureState(s);
    }

    void ProcessCallStmt(IToken tok,
      Dictionary<TypeParameter, Type> tySubst, List<TypeParameter> tyArgs,
      Expression dafnyReceiver, Bpl.Expr bReceiver,
      Method method, Label/*?*/ atLabel, List<Expression> Args,
      List<Bpl.IdentifierExpr> Lhss, List<Type> LhsTypes,
      BoogieStmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran) {

      Contract.Requires(tok != null);
      Contract.Requires(dafnyReceiver != null || bReceiver != null);
      Contract.Requires(method != null);
      Contract.Requires(VisibleInScope(method));
      Contract.Requires(method is TwoStateLemma || atLabel == null);
      Contract.Requires(Args != null);
      Contract.Requires(Lhss != null);
      Contract.Requires(LhsTypes != null);
      // Note, a Dafny class constructor is declared to have no output parameters, but it is encoded in Boogie as
      // having an output parameter.
      Contract.Requires(method is Constructor || method.Outs.Count == Lhss.Count);
      Contract.Requires(method is Constructor || method.Outs.Count == LhsTypes.Count);
      Contract.Requires(!(method is Constructor) || (method.Outs.Count == 0 && Lhss.Count == 1 && LhsTypes.Count == 1));
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);
      Contract.Requires(tySubst != null);
      Contract.Requires(tyArgs != null);
      Contract.Requires(tyArgs.Count <= tySubst.Count);  // more precisely, the members of tyArgs are required to be keys of tySubst, but this is a cheap sanity test

      // Figure out if the call is recursive or not, which will be used below to determine the need for a
      // termination check and the need to include an implicit _k-1 argument.
      bool isRecursiveCall = false;
      // consult the call graph to figure out if this is a recursive call
      var module = method.EnclosingClass.EnclosingModuleDefinition;
      if (codeContext != null && module == currentModule) {
        // Note, prefix lemmas are not recorded in the call graph, but their corresponding greatest lemmas are.
        // Similarly, an iterator is not recorded in the call graph, but its MoveNext method is.
        ICallable cllr =
          codeContext is PrefixLemma ? ((PrefixLemma)codeContext).ExtremeLemma :
          codeContext is IteratorDecl ? ((IteratorDecl)codeContext).Member_MoveNext :
          codeContext;
        if (ModuleDefinition.InSameSCC(method, cllr)) {
          isRecursiveCall = true;
        }
      }

      MethodTranslationKind kind;
      var callee = method;
      if (method is ExtremeLemma && isRecursiveCall) {
        kind = MethodTranslationKind.CoCall;
        callee = ((ExtremeLemma)method).PrefixLemma;
      } else if (method is PrefixLemma) {
        // an explicit call to a prefix lemma is allowed only inside the SCC of the corresponding greatest lemma,
        // so we consider this to be a co-call
        kind = MethodTranslationKind.CoCall;
      } else {
        kind = MethodTranslationKind.Call;
      }


      var ins = new List<Bpl.Expr>();
      if (callee is TwoStateLemma) {
        ins.Add(etran.OldAt(atLabel).HeapExpr);
        ins.Add(etran.HeapExpr);
      }
      // Add type arguments
      ins.AddRange(trTypeArgs(tySubst, tyArgs));

      // Translate receiver argument, if any
      Expression receiver = bReceiver == null ? dafnyReceiver : new BoogieWrapper(bReceiver, dafnyReceiver.Type);
      if (!method.IsStatic && !(method is Constructor)) {
        if (bReceiver == null) {
          TrStmt_CheckWellformed(dafnyReceiver, builder, locals, etran, true);
          if (!(dafnyReceiver is ThisExpr)) {
            CheckNonNull(dafnyReceiver.tok, dafnyReceiver, builder, etran, null);
          }
        }
        ins.Add(etran.TrExpr(receiver));
      } else if (receiver is StaticReceiverExpr stexpr) {
        if (stexpr.ObjectToDiscard != null) {
          TrStmt_CheckWellformed(stexpr.ObjectToDiscard, builder, locals, etran, true);
        }
      }

      // Ideally, the modifies and decreases checks would be done after the precondition check,
      // but Boogie doesn't give us a hook for that.  So, we set up our own local variables here to
      // store the actual parameters.
      // Create a local variable for each formal parameter, and assign each actual parameter to the corresponding local
      var substMap = new Dictionary<IVariable, Expression>();
      for (int i = 0; i < callee.Ins.Count; i++) {
        var formal = callee.Ins[i];
        var local = new LocalVariable(formal.RangeToken, formal.Name + "#", formal.Type.Subst(tySubst), formal.IsGhost);
        local.type = local.OptionalType;  // resolve local here
        var ie = new IdentifierExpr(local.Tok, local.AssignUniqueName(currentDeclaration.IdGenerator));
        ie.Var = local; ie.Type = ie.Var.Type;  // resolve ie here
        substMap.Add(formal, ie);
        locals.Add(new Bpl.LocalVariable(local.Tok, new Bpl.TypedIdent(local.Tok, local.AssignUniqueName(currentDeclaration.IdGenerator), TrType(local.Type))));

        var param = (Bpl.IdentifierExpr)etran.TrExpr(ie);  // TODO: is this cast always justified?
        Bpl.Expr bActual;
        if (i == 0 && method is ExtremeLemma && isRecursiveCall) {
          // Treat this call to M(args) as a call to the corresponding prefix lemma M#(_k - 1, args), so insert an argument here.
          var k = ((PrefixLemma)callee).K;
          var bplK = new Bpl.IdentifierExpr(k.tok, k.AssignUniqueName(currentDeclaration.IdGenerator), TrType(k.Type));
          if (k.Type.IsBigOrdinalType) {
            bActual = FunctionCall(k.tok, "ORD#Minus", predef.BigOrdinalType,
              bplK,
              FunctionCall(k.tok, "ORD#FromNat", predef.BigOrdinalType, Bpl.Expr.Literal(1)));
          } else {
            bActual = Bpl.Expr.Sub(bplK, Bpl.Expr.Literal(1));
          }
        } else {
          Expression actual;
          if (method is ExtremeLemma && isRecursiveCall) {
            actual = Args[i - 1];
          } else {
            actual = Args[i];
          }
          if (!(actual is DefaultValueExpression)) {
            TrStmt_CheckWellformed(actual, builder, locals, etran, true);
          }
          builder.Add(new CommentCmd("ProcessCallStmt: CheckSubrange"));
          // Check the subrange without boxing
          var beforeBox = etran.TrExpr(actual);
          CheckSubrange(actual.tok, beforeBox, actual.Type, formal.Type.Subst(tySubst), builder);
          bActual = CondApplyBox(actual.tok, beforeBox, actual.Type, formal.Type.Subst(tySubst));
        }
        Bpl.Cmd cmd = Bpl.Cmd.SimpleAssign(formal.tok, param, bActual);
        builder.Add(cmd);
        ins.Add(CondApplyBox(ToDafnyToken(param.tok), param, formal.Type.Subst(tySubst), formal.Type));
      }

      // Check that every parameter is available in the state in which the method is invoked; this means checking that it has
      // the right type and is allocated.  These checks usually hold trivially, on account of that the Dafny language only gives
      // access to expressions of the appropriate type and that are allocated in the current state.  However, if the method is
      // invoked in the 'old' state or if the method invoked is a two-state lemma with a non-new parameter, then we need to
      // check that its arguments were all available at that time as well.
      if (etran.UsesOldHeap) {
        if (!method.IsStatic && !(method is Constructor)) {
          Bpl.Expr wh = GetWhereClause(receiver.tok, etran.TrExpr(receiver), receiver.Type, etran, ISALLOC, true);
          if (wh != null) {
            var desc = new PODesc.IsAllocated("receiver argument", "in the state in which the method is invoked");
            builder.Add(Assert(receiver.tok, wh, desc));
          }
        }
        for (int i = 0; i < Args.Count; i++) {
          Expression ee = Args[i];
          Bpl.Expr wh = GetWhereClause(ee.tok, etran.TrExpr(ee), ee.Type, etran, ISALLOC, true);
          if (wh != null) {
            var desc = new PODesc.IsAllocated("argument", "in the state in which the method is invoked");
            builder.Add(Assert(ee.tok, wh, desc));
          }
        }
      } else if (method is TwoStateLemma) {
        if (!method.IsStatic) {
          Bpl.Expr wh = GetWhereClause(receiver.tok, etran.TrExpr(receiver), receiver.Type, etran.OldAt(atLabel), ISALLOC, true);
          if (wh != null) {
            var desc = new PODesc.IsAllocated("receiver argument", "in the two-state lemma's previous state");
            builder.Add(Assert(receiver.tok, wh, desc));
          }
        }
        Contract.Assert(callee.Ins.Count == Args.Count);
        for (int i = 0; i < Args.Count; i++) {
          var formal = callee.Ins[i];
          if (formal.IsOld) {
            Expression ee = Args[i];
            Bpl.Expr wh = GetWhereClause(ee.tok, etran.TrExpr(ee), ee.Type, etran.OldAt(atLabel), ISALLOC, true);
            if (wh != null) {
              var pIdx = Args.Count == 1 ? "" : " at index " + i;
              var desc = new PODesc.IsAllocated($"parameter{pIdx} ('{formal.Name}')", "in the two-state lemma's previous state");
              builder.Add(Assert(ee.tok, wh, desc));
            }
          }
        }
      }

      // Check modifies clause of a subcall is a subset of the current frame.
      if (codeContext is IMethodCodeContext) {
        var s = new Substituter(null, new Dictionary<IVariable, Expression>(), tySubst);
        CheckFrameSubset(tok, callee.Mod.Expressions.ConvertAll(s.SubstFrameExpr),
          receiver, substMap, etran, builder, new PODesc.FrameSubset("call", true), null);
      }

      // Check termination
      if (isRecursiveCall) {
        Contract.Assert(codeContext != null);
        if (codeContext is DatatypeDecl) {
          builder.Add(Assert(tok, Bpl.Expr.False, new PODesc.IsNonRecursive()));
        } else {
          List<Expression> contextDecreases = codeContext.Decreases.Expressions;
          List<Expression> calleeDecreases = callee.Decreases.Expressions;
          CheckCallTermination(tok, contextDecreases, calleeDecreases, null, receiver, substMap, tySubst, etran, etran.Old, builder, codeContext.InferredDecreases, null);
        }
      }

      // Create variables to hold the output parameters of the call, so that appropriate unboxes can be introduced.
      var outs = new List<Bpl.IdentifierExpr>();
      var tmpOuts = new List<Bpl.IdentifierExpr>();
      if (method is Constructor) {
        tmpOuts.Add(null);
        outs.Add(Lhss[0]);
      } else {
        for (int i = 0; i < Lhss.Count; i++) {
          var bLhs = Lhss[i];
          if (ModeledAsBoxType(callee.Outs[i].Type) && !ModeledAsBoxType(LhsTypes[i])) {
            // we need an Unbox
            Bpl.LocalVariable var = new Bpl.LocalVariable(bLhs.tok, new Bpl.TypedIdent(bLhs.tok, CurrentIdGenerator.FreshId("$tmp##"), predef.BoxType));
            locals.Add(var);
            Bpl.IdentifierExpr varIdE = new Bpl.IdentifierExpr(bLhs.tok, var.Name, predef.BoxType);
            tmpOuts.Add(varIdE);
            outs.Add(varIdE);
          } else {
            tmpOuts.Add(null);
            outs.Add(bLhs);
          }
        }
      }

      builder.Add(new CommentCmd("ProcessCallStmt: Make the call"));
      // Make the call
      AddReferencedMember(callee);
      Bpl.CallCmd call = Call(tok, MethodName(callee, kind), ins, outs);
      if (module != currentModule && RefinementToken.IsInherited(tok, currentModule) && (codeContext == null || !codeContext.MustReverify)) {
        // The call statement is inherited, so the refined module already checked that the precondition holds.  Note,
        // preconditions are not allowed to be strengthened, except if they use a predicate whose body has been strengthened.
        // But if the callee sits in a different module, then any predicate it uses will be treated as opaque (that is,
        // uninterpreted) anyway, so the refined module will have checked the call precondition for all possible definitions
        // of the predicate.
        call.IsFree = true;
      }
      builder.Add(call);

      // Unbox results as needed
      for (int i = 0; i < Lhss.Count; i++) {
        Bpl.IdentifierExpr bLhs = Lhss[i];
        Bpl.IdentifierExpr tmpVarIdE = tmpOuts[i];
        if (tmpVarIdE != null) {
          // Instead of an assignment:
          //    e := UnBox(tmpVar);
          // we use:
          //    havoc e; assume e == UnBox(tmpVar);
          // because that will reap the benefits of e's where clause, so that some additional type information will be known about
          // the out-parameter.
          Bpl.Cmd cmd = new Bpl.HavocCmd(bLhs.tok, new List<Bpl.IdentifierExpr> { bLhs });
          builder.Add(cmd);
          cmd = TrAssumeCmd(bLhs.tok, Bpl.Expr.Eq(bLhs, FunctionCall(bLhs.tok, BuiltinFunction.Unbox, TrType(LhsTypes[i]), tmpVarIdE)));
          builder.Add(cmd);
        }
      }
    }

    void TrForallStmtCall(IToken tok, List<BoundVar> boundVars, List<ComprehensionExpr.BoundedPool> bounds,
      Expression range, ExpressionConverter additionalRange, List<Expression> forallExpressions, CallStmt s0,
      BoogieStmtListBuilder definedness, BoogieStmtListBuilder exporter, List<Variable> locals, ExpressionTranslator etran) {
      Contract.Requires(tok != null);
      Contract.Requires(boundVars != null);
      Contract.Requires(bounds != null);
      Contract.Requires(range != null);
      // additionalRange is allowed to be null
      Contract.Requires(s0 != null);
      // definedness is allowed to be null
      Contract.Requires(exporter != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);

      // Translate:
      //   forall (x,y | Range(x,y)) {
      //     E(x,y) . M( Args(x,y) );
      //   }
      // as:
      //   if (*) {
      //     var x,y;
      //     havoc x,y;
      //     CheckWellformed( Range );
      //     assume Range(x,y);
      //     assume additionalRange;
      //     Tr( Call );
      //     assume false;
      //   } else {
      //     initHeap := $Heap;
      //     advance $Heap, Tick;
      //     assume (forall x,y :: (Range(x,y) && additionalRange)[INIT] &&
      //                           ==> Post[old($Heap) := initHeap]( E(x,y)[INIT], Args(x,y)[INIT] ));
      //   }
      // where Post(this,args) is the postcondition of method M and
      // INIT is the substitution [old($Heap),$Heap := old($Heap),initHeap].

      if (definedness != null) {
        if (boundVars.Count != 0) {
          // Note, it would be nicer (and arguably more appropriate) to do a SetupBoundVarsAsLocals
          // here (rather than a TrBoundVariables).  However, there is currently no way to apply
          // a substMap to a statement (in particular, to s.Body), so that doesn't work here.
          List<bool> freeOfAlloc = null;
          if (FrugalHeapUseX) {
            freeOfAlloc = ComprehensionExpr.BoundedPool.HasBounds(bounds, ComprehensionExpr.BoundedPool.PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc);
          }
          List<Variable> bvars = new List<Variable>();
          var ante = etran.TrBoundVariables(boundVars, bvars, true, freeOfAlloc);
          locals.AddRange(bvars);
          var havocIds = new List<Bpl.IdentifierExpr>();
          foreach (Bpl.Variable bv in bvars) {
            havocIds.Add(new Bpl.IdentifierExpr(tok, bv));
          }
          definedness.Add(new Bpl.HavocCmd(tok, havocIds));
          definedness.Add(TrAssumeCmd(tok, ante));
        }
        TrStmt_CheckWellformed(range, definedness, locals, etran, false);
        definedness.Add(TrAssumeCmd(range.tok, etran.TrExpr(range)));
        if (additionalRange != null) {
          var es = additionalRange(new Dictionary<IVariable, Expression>(), etran);
          definedness.Add(TrAssumeCmd(es.tok, es));
        }

        TrStmt(s0, definedness, locals, etran);

        definedness.Add(TrAssumeCmd(tok, Bpl.Expr.False));
      }

      // Now for the other branch, where the postcondition of the call is exported.
      {
        var initHeapVar = new Bpl.LocalVariable(tok, new Bpl.TypedIdent(tok, CurrentIdGenerator.FreshId("$initHeapForallStmt#"), predef.HeapType));
        locals.Add(initHeapVar);
        var initHeap = new Bpl.IdentifierExpr(tok, initHeapVar);
        var initEtran = new ExpressionTranslator(this, predef, initHeap, etran.Old.HeapExpr);
        // initHeap := $Heap;
        exporter.Add(Bpl.Cmd.SimpleAssign(tok, initHeap, etran.HeapExpr));
        var heapIdExpr = etran.HeapCastToIdentifierExpr;
        // advance $Heap, Tick;
        exporter.Add(new Bpl.HavocCmd(tok, new List<Bpl.IdentifierExpr> { heapIdExpr, etran.Tick() }));
        Contract.Assert(s0.Method.Mod.Expressions.Count == 0);  // checked by the resolver
        foreach (BoilerplateTriple tri in GetTwoStateBoilerplate(tok, new List<FrameExpression>(), s0.IsGhost, s0.Method.AllowsAllocation, initEtran, etran, initEtran)) {
          if (tri.IsFree) {
            exporter.Add(TrAssumeCmd(tok, tri.Expr));
          }
        }
        if (codeContext is IteratorDecl) {
          var iter = (IteratorDecl)codeContext;
          RecordNewObjectsIn_New(tok, iter, initHeap, heapIdExpr, exporter, locals, etran);
        }

        // Note, in the following, we need to do a bit of a song and dance.  The actual arguments of the
        // call should be translated using "initEtran", whereas the method postcondition should be translated
        // using "callEtran".  To accomplish this, we translate the argument and then tuck the resulting
        // Boogie expressions into BoogieExprWrappers that are used in the DafnyExpr-to-DafnyExpr substitution.
        var bvars = new List<Variable>();
        Dictionary<IVariable, Expression> substMap;
        Bpl.Trigger antitriggerBoundVarTypes;
        Bpl.Expr ante;
        var argsSubstMap = new Dictionary<IVariable, Expression>();  // maps formal arguments to actuals
        Contract.Assert(s0.Method.Ins.Count == s0.Args.Count);
        var callEtran = new ExpressionTranslator(this, predef, etran.HeapExpr, initHeap);
        Bpl.Expr post = Bpl.Expr.True;
        Bpl.Trigger tr;
        if (forallExpressions != null) {
          // translate based on the forallExpressions since the triggers are computed based on it already.
          QuantifierExpr expr = (QuantifierExpr)forallExpressions[0];
          while (expr.SplitQuantifier != null) {
            expr = (QuantifierExpr)expr.SplitQuantifierExpression;
          }
          boundVars = expr.BoundVars;
          ante = initEtran.TrBoundVariablesRename(boundVars, bvars, out substMap, out antitriggerBoundVarTypes);
          ante = BplAnd(ante, initEtran.TrExpr(Substitute(expr.Range, null, substMap)));
          if (additionalRange != null) {
            ante = BplAnd(ante, additionalRange(substMap, initEtran));
          }
          tr = TrTrigger(callEtran, expr.Attributes, expr.tok, bvars, substMap, s0.MethodSelect.TypeArgumentSubstitutionsWithParents());
          post = callEtran.TrExpr(Substitute(expr.Term, null, substMap));
        } else {
          ante = initEtran.TrBoundVariablesRename(boundVars, bvars, out substMap, out antitriggerBoundVarTypes);
          for (int i = 0; i < s0.Method.Ins.Count; i++) {
            var arg = Substitute(s0.Args[i], null, substMap, s0.MethodSelect.TypeArgumentSubstitutionsWithParents());  // substitute the renamed bound variables for the declared ones
            argsSubstMap.Add(s0.Method.Ins[i], new BoogieWrapper(initEtran.TrExpr(arg), s0.Args[i].Type));
          }
          ante = BplAnd(ante, initEtran.TrExpr(Substitute(range, null, substMap)));
          if (additionalRange != null) {
            ante = BplAnd(ante, additionalRange(substMap, initEtran));
          }
          var receiver = new BoogieWrapper(initEtran.TrExpr(Substitute(s0.Receiver, null, substMap, s0.MethodSelect.TypeArgumentSubstitutionsWithParents())), s0.Receiver.Type);
          foreach (var ens in s0.Method.Ens) {
            var p = Substitute(ens.E, receiver, argsSubstMap, s0.MethodSelect.TypeArgumentSubstitutionsWithParents());  // substitute the call's actuals for the method's formals
            post = BplAnd(post, callEtran.TrExpr(p));
          }
          tr = antitriggerBoundVarTypes;
        }

        // TRIG (forall $ih#s0#0: Seq Box :: $Is($ih#s0#0, TSeq(TChar)) && $IsAlloc($ih#s0#0, TSeq(TChar), $initHeapForallStmt#0) && Seq#Length($ih#s0#0) != 0 && Seq#Rank($ih#s0#0) < Seq#Rank(s#0) ==> (forall i#2: int :: true ==> LitInt(0) <= i#2 && i#2 < Seq#Length($ih#s0#0) ==> char#ToInt(_module.CharChar.MinChar($LS($LZ), $Heap, this, $ih#s0#0)) <= char#ToInt($Unbox(Seq#Index($ih#s0#0, i#2)): char)))
        // TRIG (forall $ih#pat0#0: Seq Box, $ih#a0#0: Seq Box :: $Is($ih#pat0#0, TSeq(_module._default.Same0$T)) && $IsAlloc($ih#pat0#0, TSeq(_module._default.Same0$T), $initHeapForallStmt#0) && $Is($ih#a0#0, TSeq(_module._default.Same0$T)) && $IsAlloc($ih#a0#0, TSeq(_module._default.Same0$T), $initHeapForallStmt#0) && Seq#Length($ih#pat0#0) <= Seq#Length($ih#a0#0) && Seq#SameUntil($ih#pat0#0, $ih#a0#0, Seq#Length($ih#pat0#0)) && (Seq#Rank($ih#pat0#0) < Seq#Rank(pat#0) || (Seq#Rank($ih#pat0#0) == Seq#Rank(pat#0) && Seq#Rank($ih#a0#0) < Seq#Rank(a#0))) ==> _module.__default.IsRelaxedPrefixAux(_module._default.Same0$T, $LS($LZ), $Heap, $ih#pat0#0, $ih#a0#0, LitInt(1)))'
        // TRIG (forall $ih#m0#0: DatatypeType, $ih#n0#0: DatatypeType :: $Is($ih#m0#0, Tclass._module.Nat()) && $IsAlloc($ih#m0#0, Tclass._module.Nat(), $initHeapForallStmt#0) && $Is($ih#n0#0, Tclass._module.Nat()) && $IsAlloc($ih#n0#0, Tclass._module.Nat(), $initHeapForallStmt#0) && Lit(true) && (DtRank($ih#m0#0) < DtRank(m#0) || (DtRank($ih#m0#0) == DtRank(m#0) && DtRank($ih#n0#0) < DtRank(n#0))) ==> _module.__default.mult($LS($LZ), $Heap, $ih#m0#0, _module.__default.plus($LS($LZ), $Heap, $ih#n0#0, $ih#n0#0)) == _module.__default.mult($LS($LZ), $Heap, _module.__default.plus($LS($LZ), $Heap, $ih#m0#0, $ih#m0#0), $ih#n0#0))
        var qq = new Bpl.ForallExpr(tok, bvars, tr, Bpl.Expr.Imp(ante, post));  // TODO: Add a SMART_TRIGGER here.  If we can't find one, abort the attempt to do induction automatically
        exporter.Add(TrAssumeCmd(tok, qq));
      }
    }

    void RecordNewObjectsIn_New(IToken tok, IteratorDecl iter, Bpl.Expr initHeap, Bpl.IdentifierExpr currentHeap,
      BoogieStmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran) {
      Contract.Requires(tok != null);
      Contract.Requires(iter != null);
      Contract.Requires(initHeap != null);
      Contract.Requires(currentHeap != null);
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);
      // Add all newly allocated objects to the set this._new
      var updatedSet = new Bpl.LocalVariable(iter.tok, new Bpl.TypedIdent(iter.tok, CurrentIdGenerator.FreshId("$iter_newUpdate"), predef.SetType(iter.tok, true, predef.BoxType)));
      locals.Add(updatedSet);
      var updatedSetIE = new Bpl.IdentifierExpr(iter.tok, updatedSet);
      // call $iter_newUpdate := $IterCollectNewObjects(initHeap, $Heap, this, _new);
      var th = new Bpl.IdentifierExpr(iter.tok, etran.This, predef.RefType);
      var nwField = new Bpl.IdentifierExpr(tok, GetField(iter.Member_New));
      Bpl.Cmd cmd = new CallCmd(iter.tok, "$IterCollectNewObjects",
        new List<Bpl.Expr>() { initHeap, etran.HeapExpr, th, nwField },
        new List<Bpl.IdentifierExpr>() { updatedSetIE });
      builder.Add(cmd);
      // $Heap[this, _new] := $iter_newUpdate;
      cmd = Bpl.Cmd.SimpleAssign(iter.tok, currentHeap, ExpressionTranslator.UpdateHeap(iter.tok, currentHeap, th, nwField, updatedSetIE));
      builder.Add(cmd);
      // assume $IsGoodHeap($Heap)
      builder.Add(AssumeGoodHeap(tok, etran));
    }

    private string GetObjFieldDetails(Expression lhs, ExpressionTranslator etran, out Bpl.Expr obj, out Bpl.Expr F) {
      string description;
      if (lhs is MemberSelectExpr) {
        var fse = (MemberSelectExpr)lhs;
        obj = etran.TrExpr(fse.Obj);
        F = GetField(fse);
        description = "an object field";
      } else if (lhs is SeqSelectExpr) {
        var sel = (SeqSelectExpr)lhs;
        obj = etran.TrExpr(sel.Seq);
        var idx = etran.TrExpr(sel.E0);
        idx = ConvertExpression(sel.E0.tok, idx, sel.E0.Type, Type.Int);
        F = FunctionCall(sel.tok, BuiltinFunction.IndexField, null, idx);
        description = "an array element";
      } else {
        MultiSelectExpr mse = (MultiSelectExpr)lhs;
        obj = etran.TrExpr(mse.Array);
        F = etran.GetArrayIndexFieldName(mse.tok, mse.Indices);
        description = "an array element";
      }
      return description;
    }
  }
}
