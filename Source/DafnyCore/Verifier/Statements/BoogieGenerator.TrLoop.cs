using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using DafnyCore.Verifier;
using Microsoft.Boogie;
using Bpl = Microsoft.Boogie;
using PODesc = Microsoft.Dafny.ProofObligationDescription;

namespace Microsoft.Dafny;

public partial class BoogieGenerator {

  private void TrAlternativeLoopStmt(AlternativeLoopStmt stmt, BoogieStmtListBuilder builder, Variables locals,
    ExpressionTranslator etran) {
    AddComment(builder, stmt, "alternative loop statement");
    var tru = Expression.CreateBoolLiteral(stmt.Tok, true);
    TrLoop(stmt, tru,
      delegate (BoogieStmtListBuilder bld, ExpressionTranslator e) {
        TrAlternatives(stmt.Alternatives, stmt.Tok,
          b => {
            foreach (var _ in Enumerable.Range(0, b.Context.ScopeDepth - builder.Context.ScopeDepth)) {
              b.Add(new ChangeScope(stmt.Tok, ChangeScope.Modes.Pop));
            }
            b.Add(new Bpl.BreakCmd(stmt.Tok, null));
          },
          bld, locals, e, stmt.IsGhost);
        InsertContinueTarget(stmt, bld);
      },
      builder, locals, etran);
  }

  private void TrForLoop(ForLoopStmt stmt, BoogieStmtListBuilder builder, Variables locals, ExpressionTranslator etran) {
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
      builder.Add(Assert(lo.tok, Bpl.Expr.Le(bLo, bHi), new ForRangeBoundsValid(lo, hi), builder.Context));
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

      var sourceBoundVar = new BoundVar(Token.NoToken, "x", Type.Int);
      var checkContext = MakeNumericBoundsSubrangeCheckContext(sourceBoundVar, dLo, dHi);
      var cre = GetSubrangeCheck(
        x.tok, x, Type.Int, indexVar.Type,
        new IdentifierExpr(Token.NoToken, sourceBoundVar),
        checkContext, out var desc);

      if (cre != null) {
        locals.Add(xVar);
        builder.Add(new Bpl.HavocCmd(tok, new List<Bpl.IdentifierExpr>() { x }));
        builder.Add(new Bpl.AssumeCmd(tok, ForLoopBounds(x, bLo, bHi)));
        List<Expression> dafnyRangeBounds = new();
        if (lo != null) {
          dafnyRangeBounds.Add(new BinaryExpr(stmt.tok, BinaryExpr.Opcode.Le, lo, dIndex));
        }
        if (hi != null) {
          dafnyRangeBounds.Add(new BinaryExpr(stmt.tok, BinaryExpr.Opcode.Le, dIndex, hi));
        }

        Expression dafnyRange = dafnyRangeBounds.Count == 1
          ? dafnyRangeBounds[0]
          : new BinaryExpr(stmt.tok, BinaryExpr.Opcode.And, dafnyRangeBounds[0], dafnyRangeBounds[1]);
        var dafnyAssertion = new ForallExpr(stmt.tok, stmt.RangeToken, new List<BoundVar> { indexVar },
          dafnyRange, new TypeTestExpr(indexVar.tok, dIndex, indexVar.Type), null);
        builder.Add(Assert(tok, cre, new ForRangeAssignable(desc, dafnyAssertion), builder.Context));
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

  private void TrWhileStmt(WhileStmt stmt, BoogieStmtListBuilder builder, Variables locals, ExpressionTranslator etran) {
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

  void TrLoop(LoopStmt s, Expression Guard, BodyTranslator/*?*/ bodyTr,
    BoogieStmtListBuilder builder, Variables locals, ExpressionTranslator etran,
    Bpl.Expr freeInvariant = null, bool includeTerminationCheck = true) {
    Contract.Requires(s != null);
    Contract.Requires(builder != null);
    Contract.Requires(locals != null);
    Contract.Requires(etran != null);

    s.ScopeDepth = builder.Context.ScopeDepth;

    var suffix = CurrentIdGenerator.FreshId("loop#");

    var theDecreases = s.Decreases.Expressions;

    Bpl.LocalVariable preLoopHeapVar = new Bpl.LocalVariable(s.Tok, new Bpl.TypedIdent(s.Tok, "$PreLoopHeap$" + suffix, predef.HeapType));
    locals.Add(preLoopHeapVar);
    Bpl.IdentifierExpr preLoopHeap = new Bpl.IdentifierExpr(s.Tok, preLoopHeapVar);
    ExpressionTranslator etranPreLoop = new ExpressionTranslator(this, predef, preLoopHeap, etran.scope);
    ExpressionTranslator updatedFrameEtran;
    string loopFrameName = FrameVariablePrefix + suffix;
    if (s.Mod.Expressions != null) {
      updatedFrameEtran = etran.WithModifiesFrame(loopFrameName);
    } else {
      updatedFrameEtran = etran;
    }

    if (s.Mod.Expressions != null) { // check well-formedness and that the modifies is a subset
      CheckFrameWellFormed(new WFOptions(), s.Mod.Expressions, locals, builder, etran);
      var desc = new ModifyFrameSubset("loop modifies clause", s.Mod.Expressions, GetContextModifiesFrames());
      CheckFrameSubset(s.Tok, s.Mod.Expressions, null, null, etran, etran.ModifiesFrame(s.Tok), builder, desc, null);
      DefineFrame(s.Tok, etran.ModifiesFrame(s.Tok), s.Mod.Expressions, builder, locals, loopFrameName);
    }
    builder.Add(Bpl.Cmd.SimpleAssign(s.Tok, preLoopHeap, etran.HeapExpr));


    var daTrackersMonotonicity = new List<Tuple<Bpl.IdentifierExpr, Bpl.IdentifierExpr>>();
    var existingLocals = locals.Values.ToList();
    foreach (var local in existingLocals) {
      if (!DefiniteAssignmentTrackers.TryGetValue(local.Name, out var dat)) {
        continue;
      }
      var preLoopDat = new Bpl.LocalVariable(dat.tok, new Bpl.TypedIdent(dat.tok, "preLoop$" + suffix + "$" + dat.Name, dat.Type));
      locals.Add(preLoopDat);
      var ie = new Bpl.IdentifierExpr(s.Tok, preLoopDat);
      daTrackersMonotonicity.Add(new Tuple<Bpl.IdentifierExpr, Bpl.IdentifierExpr>(ie, dat));
      builder.Add(Cmd.SimpleAssign(s.Tok, ie, dat));
    }

    List<Expr> initDecr = null;
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
    BoogieStmtListBuilder invDefinednessBuilder = new BoogieStmtListBuilder(this, options, builder.Context);
    foreach (AttributedExpression loopInv in s.Invariants) {
      var (errorMessage, successMessage) = CustomErrorMessage(loopInv.Attributes);
      TrStmt_CheckWellformed(loopInv.E, invDefinednessBuilder, locals, etran, false);
      invDefinednessBuilder.Add(TrAssumeCmdWithDependencies(etran, loopInv.E.tok, loopInv.E, "loop invariant"));

      invariants.Add(TrAssumeCmd(loopInv.E.tok, BplImp(w, etran.CanCallAssumption(loopInv.E))));
      var ss = TrSplitExpr(builder.Context, loopInv.E, etran, false, out var splitHappened);
      if (!splitHappened) {
        var wInv = BplImp(w, etran.TrExpr(loopInv.E));
        invariants.Add(Assert(loopInv.E.tok, wInv, new LoopInvariant(loopInv.E, errorMessage, successMessage), builder.Context));
      } else {
        foreach (var split in ss) {
          var wInv = Bpl.Expr.Binary(split.E.tok, BinaryOperator.Opcode.Imp, w, split.E);
          if (split.IsChecked) {
            invariants.Add(Assert(split.Tok, wInv, new LoopInvariant(loopInv.E, errorMessage, successMessage), builder.Context));  // TODO: it would be fine to have this use {:subsumption 0}
          } else {
            var cmd = TrAssumeCmd(split.E.tok, wInv);
            proofDependencies?.AddProofDependencyId(cmd, loopInv.E.tok, new InvariantDependency(loopInv.E));
            invariants.Add(cmd);
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
          invariants.Add(Assert(s.Tok, tri.Expr, new Microsoft.Dafny.BoilerplateTriple(tri.ErrorMessage, tri.SuccessMessage, tri.Comment), builder.Context));
        }
      }
      // add a free invariant which says that the heap hasn't changed outside of the modifies clause.
      invariants.Add(TrAssumeCmd(s.Tok, FrameConditionUsingDefinedFrame(s.Tok, etranPreLoop, etran, updatedFrameEtran, updatedFrameEtran.ModifiesFrame(s.Tok))));
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
      Bpl.Expr monotonic = BplImp(pair.Item1, pair.Item2);
      invariants.Add(TrAssumeCmd(s.Tok, monotonic));
    }

    // include a free invariant that says that all completed iterations so far have only decreased the termination metric
    if (initDecr != null) {
      var toks = new List<IToken>();
      var decrs = new List<Expr>();
      var decrsDafny = new List<Expression>();
      var initDecrsDafny = new List<Expression>();
      var prevGhostLocals = new List<VarDeclStmt>();
      foreach (Expression e in theDecreases) {
        toks.Add(e.tok);
        decrsDafny.Add(e);
        decrs.Add(etran.TrExpr(e));
        var (prevVars, eInit) = TranslateToLoopEntry(s, e, "LoopEntry");
        prevGhostLocals.AddRange(prevVars);
        initDecrsDafny.Add(eInit);
      }
      Bpl.Expr decrCheck = DecreasesCheck(toks, prevGhostLocals, decrsDafny, initDecrsDafny, decrs, initDecr,
        null, null, true, false);
      invariants.Add(TrAssumeCmd(s.Tok, decrCheck));
    }

    var loopBodyBuilder = new BoogieStmtListBuilder(this, options, builder.Context);
    loopBodyBuilder.AddCaptureState(s.Tok, true, CaptureStateExtensions.AfterLoopIterationsStateMarker);

    // As the first thing inside the loop, generate:  if (!w) { CheckWellformed(inv); assume false; }
    invDefinednessBuilder.Add(TrAssumeCmd(s.Tok, Bpl.Expr.False));
    loopBodyBuilder.Add(new Bpl.IfCmd(s.Tok, Bpl.Expr.Not(w), invDefinednessBuilder.Collect(s.Tok), null, null));

    // Generate:  CheckWellformed(guard); if (!guard) { break; }
    // but if this is a body-less loop, put all of that inside:  if (*) { ... }
    // Without this, Boogie's abstract interpreter may figure out that the loop guard is always false
    // on entry to the loop, and then Boogie wouldn't consider this a loop at all. (See also comment
    // in methods GuardAlwaysHoldsOnEntry_BodyLessLoop and GuardAlwaysHoldsOnEntry_LoopWithBody in
    // Test/dafny0/DirtyLoops.dfy.)
    var isBodyLessLoop = s is OneBodyLoopStmt { BodySurrogate: { } };
    var whereToBuildLoopGuard = isBodyLessLoop ? new BoogieStmtListBuilder(this, options, builder.Context) : loopBodyBuilder;
    Bpl.Expr guard = null;
    if (Guard != null) {
      TrStmt_CheckWellformed(Guard, whereToBuildLoopGuard, locals, etran, true);
      guard = Bpl.Expr.Not(etran.TrExpr(Guard));
    }
    var guardBreak = new BoogieStmtListBuilder(this, options, builder.Context);
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
        var decrs = new List<Expr>();
        var decrsDafny = new List<Expression>();
        var initDecrsDafny = new List<Expression>();
        var prevGhostLocals = new List<VarDeclStmt>();
        foreach (Expression e in theDecreases) {
          toks.Add(e.tok);
          // Note: the label "LoopEntry" doesn't exist in the program, and is
          // useful only for explanatory purposes.
          decrsDafny.Add(e);
          var (prevVars, eInit) = TranslateToLoopEntry(s, e, "LoopEntry");
          prevGhostLocals.AddRange(prevVars);
          initDecrsDafny.Add(eInit);
          decrs.Add(etran.TrExpr(e));
        }
        if (includeTerminationCheck) {
          AddComment(loopBodyBuilder, s, "loop termination check");
          Bpl.Expr decrCheck = DecreasesCheck(toks, prevGhostLocals, decrsDafny, initDecrsDafny, decrs, oldBfs,
            loopBodyBuilder, " at end of loop iteration", false, false);
          var description = new
            Terminates(s.InferredDecreases, prevGhostLocals, null, initDecrsDafny, theDecreases, false);
          loopBodyBuilder.Add(Assert(s.Tok, decrCheck, description, builder.Context));
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
      loopBodyBuilder.Add(TrAssumeCmd(s.Tok, etran.CanCallAssumption(allInvariants)));
    }

    Bpl.StmtList body = loopBodyBuilder.Collect(s.Tok);
    builder.Add(new Bpl.WhileCmd(s.Tok, Bpl.Expr.True, invariants, new List<CallCmd>(), body));
  }

  // Return the version of e that holds at the beginnging of the loop,
  // Along with the local variable assignments that need to happen at
  // the beginning of the loop for it to be valid.
  private (List<VarDeclStmt>, Expression) TranslateToLoopEntry(LoopStmt loop, Expression e, string loopLabel) {
    var prevGhostLocals = new List<VarDeclStmt>();
    Expression olde = new OldExpr(e.tok, e, loopLabel) {
      Type = e.Type
    };

    var subStmts = TransitiveSubstatements(loop);
    var modifiedVars =
      subStmts
        .OfType<SingleAssignStmt>()
        .Select(s => s.Lhs)
        .OfType<IdentifierExpr>();
    foreach (var ie in modifiedVars) {
      var prevName = $"prev_{ie.Name}";
      var prevDecl = Statement.CreateLocalVariable(RangeToken.NoToken, prevName, ie);
      var prevRef = Expression.CreateIdentExpr(prevDecl.Locals[0]);
      olde = Substitute(olde, ie.Var, prevRef);
      prevGhostLocals.Add(prevDecl);
    }

    return (prevGhostLocals, olde);

  }

  void InsertContinueTarget(LoopStmt loop, BoogieStmtListBuilder builder) {
    Contract.Requires(loop != null);
    Contract.Requires(builder != null);
    if (loop.Labels != null) {
      builder.AddLabelCmd("continue_" + loop.Labels.Data.AssignUniqueId(CurrentIdGenerator));
    }
  }
}