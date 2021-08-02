using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny
{
  public partial class Translator
  {
    private void TrStmt(Statement stmt, BoogieStmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran)
    {
      Contract.Requires(stmt != null);
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);
      Contract.Requires(codeContext != null && predef != null);
      Contract.Ensures(fuelContext == Contract.OldValue(fuelContext));

      stmtContext = StmtType.NONE;
      adjustFuelForExists = true;  // fuel for exists might need to be adjusted based on whether it's in an assert or assume stmt.
      if (stmt is PredicateStmt) {
        var stmtBuilder = new BoogieStmtListBuilder(this);
        string errorMessage = CustomErrorMessage(stmt.Attributes);
        this.fuelContext = FuelSetting.ExpandFuelContext(stmt.Attributes, stmt.Tok, this.fuelContext, this.reporter);
        var defineFuel = DefineFuelConstant(stmt.Tok, stmt.Attributes, stmtBuilder, etran);
        var b = defineFuel ? stmtBuilder : builder;
        if (stmt is AssertStmt || DafnyOptions.O.DisallowSoundnessCheating) {
          stmtContext = StmtType.ASSERT;
          AddComment(b, stmt, "assert statement");
          PredicateStmt s = (PredicateStmt)stmt;
          TrStmt_CheckWellformed(s.Expr, b, locals, etran, false);
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
          var ss = TrSplitExpr(s.Expr, etran, true, out splitHappened);
          if (!splitHappened) {
            var tok = enclosingToken == null ? s.Expr.tok : new NestedToken(enclosingToken, s.Expr.tok);
            (proofBuilder ?? b).Add(Assert(tok, etran.TrExpr(s.Expr), errorMessage ?? "assertion violation", stmt.Tok, etran.TrAttributes(stmt.Attributes, null)));
          } else {
            foreach (var split in ss) {
              if (split.IsChecked) {
                var tok = enclosingToken == null ? split.E.tok : new NestedToken(enclosingToken, split.E.tok);
                (proofBuilder ?? b).Add(AssertNS(tok, split.E, errorMessage ?? "assertion violation", stmt.Tok, etran.TrAttributes(stmt.Attributes, null)));  // attributes go on every split
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
              foreach (var v in ComputeFreeVariables(assertStmt.Expr)) {
                if (v is LocalVariable) {
                  var vcopy = new LocalVariable(stmt.Tok, stmt.Tok, string.Format("##{0}#{1}", name, v.Name), v.Type, v.IsGhost);
                  vcopy.type = vcopy.OptionalType;  // resolve local here
                  IdentifierExpr ie = new IdentifierExpr(vcopy.Tok, vcopy.AssignUniqueName(currentDeclaration.IdGenerator));
                  ie.Var = vcopy; ie.Type = ie.Var.Type;  // resolve ie here
                  substMap.Add(v, ie);
                  locals.Add(new Bpl.LocalVariable(vcopy.Tok, new Bpl.TypedIdent(vcopy.Tok, vcopy.AssignUniqueName(currentDeclaration.IdGenerator), TrType(vcopy.Type))));
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
              b.Add(TrAssumeCmd(stmt.Tok, etran.TrExpr(s.Expr)));
              stmtContext = StmtType.NONE;
            }
          }
          if (defineFuel) {
            var ifCmd = new Bpl.IfCmd(s.Tok, null, b.Collect(s.Tok), null, null);  // BUGBUG: shouldn't this first append "assume false" to "b"? (use PathAsideBlock to do this)  --KRML
            builder.Add(ifCmd);
            // Adding the assume stmt, resetting the stmtContext
            stmtContext = StmtType.ASSUME;
            adjustFuelForExists = true;
            builder.Add(TrAssumeCmd(stmt.Tok, etran.TrExpr(s.Expr)));
            stmtContext = StmtType.NONE;
          }
        } else if (stmt is ExpectStmt) {
          AddComment(builder, stmt, "expect statement");
          ExpectStmt s = (ExpectStmt)stmt;
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

          stmtContext = StmtType.NONE;  // done with translating expect stmt.
        } else if (stmt is AssumeStmt) {
          AddComment(builder, stmt, "assume statement");
          AssumeStmt s = (AssumeStmt)stmt;
          stmtContext = StmtType.ASSUME;
          TrStmt_CheckWellformed(s.Expr, builder, locals, etran, false);
          builder.Add(TrAssumeCmd(stmt.Tok, etran.TrExpr(s.Expr), etran.TrAttributes(stmt.Attributes, null)));
          stmtContext = StmtType.NONE;  // done with translating assume stmt.
        }
        this.fuelContext = FuelSetting.PopFuelContext();
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
        foreach (var resolved in s.ResolvedStatements) {
          TrStmt(resolved, builder, locals, etran);
        }

      } else if (stmt is BreakStmt) {
        AddComment(builder, stmt, "break statement");
        var s = (BreakStmt)stmt;
        builder.Add(new GotoCmd(s.Tok, new List<String> { "after_" + s.TargetStmt.Labels.Data.AssignUniqueId(CurrentIdGenerator) }));
      } else if (stmt is ReturnStmt) {
        var s = (ReturnStmt)stmt;
        AddComment(builder, stmt, "return statement");
        if (s.ReverifyPost) {
          // $_reverifyPost := true;
          builder.Add(Bpl.Cmd.SimpleAssign(s.Tok, new Bpl.IdentifierExpr(s.Tok, "$_reverifyPost", Bpl.Type.Bool), Bpl.Expr.True));
        }
        if (s.hiddenUpdate != null) {
          TrStmt(s.hiddenUpdate, builder, locals, etran);
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
        if (s.hiddenUpdate != null) {
          TrStmt(s.hiddenUpdate, builder, locals, etran);
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
          var cmd = Bpl.Cmd.SimpleAssign(s.Tok, (Bpl.IdentifierExpr/*TODO: this cast is rather dubious*/)etran.HeapExpr,
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
            if (RefinementToken.IsInherited(split.E.tok, currentModule)) {
              // this postcondition was inherited into this module, so just ignore it
            } else if (split.IsChecked) {
              var yieldToken = new NestedToken(s.Tok, split.E.tok);
              builder.Add(AssertNS(yieldToken, split.E, "possible violation of yield-ensures condition", stmt.Tok, null));
            }
          }
          builder.Add(TrAssumeCmd(stmt.Tok, yeEtran.TrExpr(p.E)));
        }
        YieldHavoc(iter.tok, iter, builder, etran);
        builder.Add(CaptureState(s));

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
        //     defass$x := true;
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
        builder.Add(CaptureState(s));  // just do one capture state--here, at the very end (that is, don't do one before the assume)

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
          builder.Add(CaptureState(s));
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
        fields.Iter(f => AddDefiniteAssignmentTrackerSurrogate(f, cl, locals));

        Contract.Assert(!inBodyInitContext);
        inBodyInitContext = true;
        TrStmtList(s.BodyInit, builder, locals, etran);
        Contract.Assert(inBodyInitContext);
        inBodyInitContext = false;

        // The "new;" translates into an allocation of "this"
        AddComment(builder, stmt, "new;");
        fields.Iter(f => CheckDefiniteAssignmentSurrogate(s.SeparatorTok ?? s.EndTok, f, true, builder));
        fields.Iter(f => RemoveDefiniteAssignmentTrackerSurrogate(f));
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
      } else if (stmt is IfStmt) {
        AddComment(builder, stmt, "if statement");
        IfStmt s = (IfStmt)stmt;
        Expression guard;
        if (s.Guard == null) {
          guard = null;
        } else {
          guard = s.IsBindingGuard ? AlphaRename((ExistsExpr)s.Guard, "eg$") : s.Guard;
          TrStmt_CheckWellformed(guard, builder, locals, etran, true);
        }
        BoogieStmtListBuilder b = new BoogieStmtListBuilder(this);
        if (s.IsBindingGuard) {
          CurrentIdGenerator.Push();
          var exists = (ExistsExpr)s.Guard;  // the original (that is, not alpha-renamed) guard
          IntroduceAndAssignExistentialVars(exists, b, builder, locals, etran, stmt.IsGhost);
          CurrentIdGenerator.Pop();
        }
        CurrentIdGenerator.Push();
        Bpl.StmtList thn = TrStmt2StmtList(b, s.Thn, locals, etran);
        CurrentIdGenerator.Pop();
        Bpl.StmtList els;
        Bpl.IfCmd elsIf = null;
        b = new BoogieStmtListBuilder(this);
        if (s.IsBindingGuard) {
          b.Add(TrAssumeCmd(guard.tok, Bpl.Expr.Not(etran.TrExpr(guard))));
        }
        if (s.Els == null) {
          els = b.Collect(s.Tok);
        } else {
          CurrentIdGenerator.Push();
          els = TrStmt2StmtList(b, s.Els, locals, etran);
          CurrentIdGenerator.Pop();
          if (els.BigBlocks.Count == 1) {
            Bpl.BigBlock bb = els.BigBlocks[0];
            if (bb.LabelName == null && bb.simpleCmds.Count == 0 && bb.ec is Bpl.IfCmd) {
              elsIf = (Bpl.IfCmd)bb.ec;
              els = null;
            }
          }
        }
        builder.Add(new Bpl.IfCmd(stmt.Tok, guard == null || s.IsBindingGuard ? null : etran.TrExpr(guard), thn, elsIf, els));

      } else if (stmt is AlternativeStmt) {
        AddComment(builder, stmt, "alternative statement");
        var s = (AlternativeStmt)stmt;
        var elseCase = Assert(s.Tok, Bpl.Expr.False, "alternative cases fail to cover all possibilties");
        TrAlternatives(s.Alternatives, elseCase, null, builder, locals, etran, stmt.IsGhost);

      } else if (stmt is WhileStmt) {
        AddComment(builder, stmt, "while statement");
        this.fuelContext = FuelSetting.ExpandFuelContext(stmt.Attributes, stmt.Tok, this.fuelContext, this.reporter);
        DefineFuelConstant(stmt.Tok, stmt.Attributes, builder, etran);
        var s = (WhileStmt)stmt;
        BodyTranslator bodyTr = null;
        if (s.Body != null) {
          bodyTr = delegate(BoogieStmtListBuilder bld, ExpressionTranslator e) {
            CurrentIdGenerator.Push();
            TrStmt(s.Body, bld, locals, e);
            CurrentIdGenerator.Pop();
          };
        }
        TrLoop(s, s.Guard, bodyTr, builder, locals, etran);
        this.fuelContext = FuelSetting.PopFuelContext();
      } else if (stmt is AlternativeLoopStmt) {
        AddComment(builder, stmt, "alternative loop statement");
        var s = (AlternativeLoopStmt)stmt;
        var tru = new LiteralExpr(s.Tok, true);
        tru.Type = Type.Bool; // resolve here
        TrLoop(s, tru,
          delegate(BoogieStmtListBuilder bld, ExpressionTranslator e) {
            TrAlternatives(s.Alternatives, null, new Bpl.BreakCmd(s.Tok, null), bld, locals, e, stmt.IsGhost);
          },
          builder, locals, etran);

      } else if (stmt is ForLoopStmt) {
        var s = (ForLoopStmt)stmt;
        AddComment(builder, stmt, "for-loop statement");

        var indexVar = s.LoopIndex;
        var indexVarName = indexVar.AssignUniqueName(currentDeclaration.IdGenerator);
        var dIndex = new IdentifierExpr(indexVar.tok, indexVar);
        var bIndexVar = new Bpl.LocalVariable(indexVar.tok, new Bpl.TypedIdent(indexVar.Tok, indexVarName, TrType(indexVar.Type)));
        locals.Add(bIndexVar);
        var bIndex = new Bpl.IdentifierExpr(indexVar.tok, indexVarName);

        var lo = s.GoingUp ? s.Start : s.End;
        var hi = s.GoingUp ? s.End : s.Start;
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
          builder.Add(Assert(lo.tok, Bpl.Expr.Le(bLo, bHi), "lower bound must not exceed upper bound"));
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
          string msg;
          var cre = GetSubrangeCheck(x, Type.Int, indexVar.Type, out msg);
          if (cre != null) {
            locals.Add(xVar);
            builder.Add(new Bpl.HavocCmd(tok, new List<Bpl.IdentifierExpr>() { x }));
            builder.Add(new Bpl.AssumeCmd(tok, ForLoopBounds(x, bLo, bHi)));
            builder.Add(Assert(tok, cre, "entire range must be assignable to index variable, but some " + msg));
          }
        }

        // initialize the index variable
        builder.Add(Bpl.Cmd.SimpleAssign(indexVar.tok, bIndex, s.GoingUp ? bLo : bHi));

        // build the guard expression
        Expression guard;
        if (lo == null || hi == null) {
          guard = LiteralExpr.CreateBoolLiteral(s.Tok, true);
        } else {
          guard = Expression.CreateNot(s.Tok, Expression.CreateEq(dIndex, s.GoingUp ? dHi : dLo, indexVar.Type));
        }

        // free invariant lo <= i <= hi
        var freeInvariant = ForLoopBounds(bIndex, bLo, bHi);

        BodyTranslator bodyTr = null;
        if (s.Body != null) {
          bodyTr = delegate(BoogieStmtListBuilder bld, ExpressionTranslator e) {
            CurrentIdGenerator.Push();
            if (!s.GoingUp) {
              bld.Add(Bpl.Cmd.SimpleAssign(s.Tok, bIndex, Bpl.Expr.Sub(bIndex, Bpl.Expr.Literal(1))));
            }
            TrStmt(s.Body, bld, locals, e);
            if (s.GoingUp) {
              bld.Add(Bpl.Cmd.SimpleAssign(s.Tok, bIndex, Bpl.Expr.Add(bIndex, Bpl.Expr.Literal(1))));
            }
            CurrentIdGenerator.Pop();
          };
        }

        TrLoop(s, guard, bodyTr, builder, locals, etran, freeInvariant, s.Decreases.Expressions.Count != 0);

      } else if (stmt is ModifyStmt) {
        AddComment(builder, stmt, "modify statement");
        var s = (ModifyStmt)stmt;
        // check well-formedness of the modifies clauses
        CheckFrameWellFormed(new WFOptions(), s.Mod.Expressions, locals, builder, etran);
        // check that the modifies is a subset
        CheckFrameSubset(s.Tok, s.Mod.Expressions, null, null, etran, builder, "modify statement may violate context's modifies clause", null);
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
          builder.Add(new Bpl.HavocCmd(s.Tok, new List<Bpl.IdentifierExpr> { (Bpl.IdentifierExpr/*TODO: this cast is rather dubious*/)etran.HeapExpr }));
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
        builder.Add(CaptureState(stmt));

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
            builder.Add(CaptureState(stmt));
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
            builder.Add(CaptureState(stmt));
          }

        } else if (s.Kind == ForallStmt.BodyKind.Proof) {
          AddComment(builder, stmt, "forall statement (proof)");
          var definedness = new BoogieStmtListBuilder(this);
          var exporter = new BoogieStmtListBuilder(this);
          DefineFuelConstant(stmt.Tok, stmt.Attributes, definedness, etran);
          TrForallProof(s, definedness, exporter, locals, etran);
          // All done, so put the two pieces together
          builder.Add(new Bpl.IfCmd(s.Tok, null, definedness.Collect(s.Tok), null, exporter.Collect(s.Tok)));
          builder.Add(CaptureState(stmt));

        } else {
          Contract.Assert(false);  // unexpected kind
        }
        CurrentIdGenerator.Pop();
        this.fuelContext = FuelSetting.PopFuelContext();
      } else if (stmt is CalcStmt) {
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
        var s = (CalcStmt)stmt;
        Contract.Assert(s.Steps.Count == s.Hints.Count); // established by the resolver
        AddComment(builder, stmt, "calc statement");
        this.fuelContext = FuelSetting.ExpandFuelContext(stmt.Attributes, stmt.Tok, this.fuelContext, this.reporter);
        DefineFuelConstant(stmt.Tok, stmt.Attributes, builder, etran);
        CurrentIdGenerator.Push();  // put the entire calc statement within its own sub-branch
        if (s.Lines.Count > 0) {
          Bpl.IfCmd ifCmd = null;
          BoogieStmtListBuilder b;
          // if the dangling hint is empty, do not generate anything for the dummy step
          var stepCount = s.Hints.Last().Body.Count == 0 ? s.Steps.Count - 1 : s.Steps.Count;
          // check steps:
          for (int i = stepCount; 0 <= --i; ) {
            b = new BoogieStmtListBuilder(this);
            // assume wf[line<i>]:
            AddComment(b, stmt, "assume wf[lhs]");
            CurrentIdGenerator.Push();
            assertAsAssume = true;
            TrStmt_CheckWellformed(CalcStmt.Lhs(s.Steps[i]), b, locals, etran, false);
            assertAsAssume = false;
            if (s.Steps[i] is BinaryExpr && (((BinaryExpr)s.Steps[i]).ResolvedOp == BinaryExpr.ResolvedOpcode.Imp)) {
              // assume line<i>:
              AddComment(b, stmt, "assume lhs");
              b.Add(TrAssumeCmd(s.Tok, etran.TrExpr(CalcStmt.Lhs(s.Steps[i]))));
            }
            // hint:
            AddComment(b, stmt, "Hint" + i.ToString());
            TrStmt(s.Hints[i], b, locals, etran);
            if (i < s.Steps.Count - 1) { // non-dummy step
              // check well formedness of the goal line:
              AddComment(b, stmt, "assert wf[rhs]");
              if (s.Steps[i] is TernaryExpr) {
                // check the prefix-equality limit
                var index = ((TernaryExpr) s.Steps[i]).E0;
                TrStmt_CheckWellformed(index, b, locals, etran, false);
                if (index.Type.IsNumericBased(Type.NumericPersuasion.Int)) {
                  b.Add(AssertNS(index.tok, Bpl.Expr.Le(Bpl.Expr.Literal(0), etran.TrExpr(index)), "prefix-equality limit must be at least 0"));
                }
              }
              TrStmt_CheckWellformed(CalcStmt.Rhs(s.Steps[i]), b, locals, etran, false);
              bool splitHappened;
              var ss = TrSplitExpr(s.Steps[i], etran, true, out splitHappened);
              // assert step:
              AddComment(b, stmt, "assert line" + i.ToString() + " " + (s.StepOps[i] ?? s.Op).ToString() + " line" + (i + 1).ToString());
              if (!splitHappened) {
                b.Add(AssertNS(s.Lines[i + 1].tok, etran.TrExpr(s.Steps[i]), "the calculation step between the previous line and this line might not hold"));
              } else {
                foreach (var split in ss) {
                  if (split.IsChecked) {
                    b.Add(AssertNS(s.Lines[i + 1].tok, split.E, "the calculation step between the previous line and this line might not hold"));
                  }
                }
              }
            }
            b.Add(TrAssumeCmd(s.Tok, Bpl.Expr.False));
            ifCmd = new Bpl.IfCmd(s.Tok, null, b.Collect(s.Tok), ifCmd, null);
            CurrentIdGenerator.Pop();
          }
          // check well formedness of the first line:
          b = new BoogieStmtListBuilder(this);
          AddComment(b, stmt, "assert wf[initial]");
          Contract.Assert(s.Result != null); // established by the resolver
          TrStmt_CheckWellformed(CalcStmt.Lhs(s.Result), b, locals, etran, false);
          b.Add(TrAssumeCmd(s.Tok, Bpl.Expr.False));
          ifCmd = new Bpl.IfCmd(s.Tok, null, b.Collect(s.Tok), ifCmd, null);
          builder.Add(ifCmd);
          // assume result:
          if (s.Steps.Count > 1) {
            builder.Add(TrAssumeCmd(s.Tok, etran.TrExpr(s.Result)));
          }
        }
        CurrentIdGenerator.Pop();
        this.fuelContext = FuelSetting.PopFuelContext();
      } else if (stmt is ConcreteSyntaxStatement) {
        ConcreteSyntaxStatement s = (ConcreteSyntaxStatement)stmt;
        TrStmt(s.ResolvedStatement, builder, locals, etran);
      } else if (stmt is MatchStmt) {
        var s = (MatchStmt)stmt;
        TrStmt_CheckWellformed(s.Source, builder, locals, etran, true);
        Bpl.Expr source = etran.TrExpr(s.Source);
        var b = new BoogieStmtListBuilder(this);
        b.Add(TrAssumeCmd(stmt.Tok, Bpl.Expr.False));
        Bpl.StmtList els = b.Collect(stmt.Tok);
        Bpl.IfCmd ifCmd = null;
        foreach (var missingCtor in s.MissingCases) {
          // havoc all bound variables
          b = new BoogieStmtListBuilder(this);
          List<Variable> newLocals = new List<Variable>();
          Bpl.Expr r = CtorInvocation(s.Tok, missingCtor, etran, newLocals, b);
          locals.AddRange(newLocals);

          if (newLocals.Count != 0)
          {
            List<Bpl.IdentifierExpr> havocIds = new List<Bpl.IdentifierExpr>();
            foreach (Variable local in newLocals) {
              havocIds.Add(new Bpl.IdentifierExpr(local.tok, local));
            }
            builder.Add(new Bpl.HavocCmd(s.Tok, havocIds));
          }
          String missingStr = s.Context.FillHole(new IdCtx(new KeyValuePair<string, DatatypeCtor>(missingCtor.Name, missingCtor))).AbstractAllHoles().ToString();
          b.Add(Assert(s.Tok, Bpl.Expr.False, "missing case in match statement: " + missingStr));

          Bpl.Expr guard = Bpl.Expr.Eq(source, r);
          ifCmd = new Bpl.IfCmd(s.Tok, guard, b.Collect(s.Tok), ifCmd, els);
          els = null;
        }
        for (int i = s.Cases.Count; 0 <= --i; ) {
          var mc = (MatchCaseStmt)s.Cases[i];
          CurrentIdGenerator.Push();
          // havoc all bound variables
          b = new BoogieStmtListBuilder(this);
          List<Variable> newLocals = new List<Variable>();
          Bpl.Expr r = CtorInvocation(mc, s.Source.Type, etran, newLocals, b, s.IsGhost ? NOALLOC : ISALLOC);
          locals.AddRange(newLocals);

          if (newLocals.Count != 0)
          {
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
        Contract.Assert(ifCmd != null);  // follows from the fact that s.Cases.Count + s.MissingCases.Count != 0.
        builder.Add(ifCmd);

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
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected statement
      }
    }
  }
}