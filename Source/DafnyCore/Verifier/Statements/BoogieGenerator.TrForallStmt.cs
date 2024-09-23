using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;
using Bpl = Microsoft.Boogie;
using PODesc = Microsoft.Dafny.ProofObligationDescription;

namespace Microsoft.Dafny;

public partial class BoogieGenerator {


  private void TrForallStmt(BoogieStmtListBuilder builder, Variables locals, ExpressionTranslator etran,
    ForallStmt forallStmt) {
    this.fuelContext = FuelSetting.ExpandFuelContext(forallStmt.Attributes, forallStmt.Tok, this.fuelContext, this.reporter);

    CurrentIdGenerator.Push();
    if (forallStmt.Kind == ForallStmt.BodyKind.Assign) {
      AddComment(builder, forallStmt, "forall statement (assign)");
      Contract.Assert(forallStmt.Ens.Count == 0);
      if (forallStmt.BoundVars.Count == 0) {
        TrStmt(forallStmt.Body, builder, locals, etran);
      } else {
        var s0 = (SingleAssignStmt)forallStmt.S0;
        var definedness = new BoogieStmtListBuilder(this, options, builder.Context);
        var updater = new BoogieStmtListBuilder(this, options, builder.Context);
        DefineFuelConstant(forallStmt.Tok, forallStmt.Attributes, definedness, etran);
        TrForallAssign(forallStmt, s0, definedness, updater, locals, etran);
        // All done, so put the two pieces together
        builder.Add(new Bpl.IfCmd(forallStmt.Tok, null, definedness.Collect(forallStmt.Tok), null, updater.Collect(forallStmt.Tok)));
        builder.AddCaptureState(forallStmt);
      }

    } else if (forallStmt.Kind == ForallStmt.BodyKind.Call) {
      AddComment(builder, forallStmt, "forall statement (call)");
      Contract.Assert(forallStmt.Ens.Count == 0);
      if (forallStmt.BoundVars.Count == 0) {
        Contract.Assert(LiteralExpr.IsTrue(forallStmt.Range));  // follows from the invariant of ForallStmt
        TrStmt(forallStmt.Body, builder, locals, etran);
      } else {
        var s0 = (CallStmt)forallStmt.S0;
        if (Attributes.Contains(forallStmt.Attributes, "_trustWellformed")) {
          TrForallStmtCall(forallStmt.Tok, forallStmt.BoundVars, forallStmt.Bounds, forallStmt.Range, null, forallStmt.EffectiveEnsuresClauses, s0, null, builder, locals, etran);
        } else {
          var definedness = new BoogieStmtListBuilder(this, options, builder.Context);
          DefineFuelConstant(forallStmt.Tok, forallStmt.Attributes, definedness, etran);
          var exporter = new BoogieStmtListBuilder(this, options, builder.Context);
          TrForallStmtCall(forallStmt.Tok, forallStmt.BoundVars, forallStmt.Bounds, forallStmt.Range, null, forallStmt.EffectiveEnsuresClauses, s0, definedness, exporter, locals, etran);
          // All done, so put the two pieces together
          builder.Add(new Bpl.IfCmd(forallStmt.Tok, null, definedness.Collect(forallStmt.Tok), null, exporter.Collect(forallStmt.Tok)));
        }
        builder.AddCaptureState(forallStmt);
      }

    } else if (forallStmt.Kind == ForallStmt.BodyKind.Proof) {
      AddComment(builder, forallStmt, "forall statement (proof)");
      var definedness = new BoogieStmtListBuilder(this, options, builder.Context);
      var exporter = new BoogieStmtListBuilder(this, options, builder.Context);
      DefineFuelConstant(forallStmt.Tok, forallStmt.Attributes, definedness, etran);
      TrForallProof(forallStmt, definedness, exporter, locals, etran);
      // All done, so put the two pieces together
      builder.Add(new Bpl.IfCmd(forallStmt.Tok, null, definedness.Collect(forallStmt.Tok), null, exporter.Collect(forallStmt.Tok)));
      builder.AddCaptureState(forallStmt);

    } else {
      Contract.Assert(false);  // unexpected kind
    }
    CurrentIdGenerator.Pop();
    this.fuelContext = FuelSetting.PopFuelContext();
  }


  void TrForallStmtCall(IToken tok, List<BoundVar> boundVars, List<BoundedPool> bounds,
    Expression range, ExpressionConverter additionalRange, List<Expression> forallExpressions, CallStmt s0,
    BoogieStmtListBuilder definedness, BoogieStmtListBuilder exporter, Variables locals, ExpressionTranslator etran) {
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
    //     advance $Heap;
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
        List<bool> freeOfAlloc = BoundedPool.HasBounds(bounds, BoundedPool.PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc);
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
      var initEtran = new ExpressionTranslator(this, predef, initHeap, etran.Old.HeapExpr, etran.scope);
      // initHeap := $Heap;
      exporter.Add(Bpl.Cmd.SimpleAssign(tok, initHeap, etran.HeapExpr));
      var heapIdExpr = etran.HeapCastToIdentifierExpr;
      // advance $Heap;
      exporter.Add(new Bpl.HavocCmd(tok, new List<Bpl.IdentifierExpr> { heapIdExpr }));
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
      var callEtran = new ExpressionTranslator(this, predef, etran.HeapExpr, initHeap, etran.scope);
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

      // TRIG (forall $ih#s0#0: Seq :: $Is($ih#s0#0, TSeq(TChar)) && $IsAlloc($ih#s0#0, TSeq(TChar), $initHeapForallStmt#0) && Seq#Length($ih#s0#0) != 0 && Seq#Rank($ih#s0#0) < Seq#Rank(s#0) ==> (forall i#2: int :: true ==> LitInt(0) <= i#2 && i#2 < Seq#Length($ih#s0#0) ==> char#ToInt(_module.CharChar.MinChar($LS($LZ), $Heap, this, $ih#s0#0)) <= char#ToInt($Unbox(Seq#Index($ih#s0#0, i#2)): char)))
      // TRIG (forall $ih#pat0#0: Seq, $ih#a0#0: Seq :: $Is($ih#pat0#0, TSeq(_module._default.Same0$T)) && $IsAlloc($ih#pat0#0, TSeq(_module._default.Same0$T), $initHeapForallStmt#0) && $Is($ih#a0#0, TSeq(_module._default.Same0$T)) && $IsAlloc($ih#a0#0, TSeq(_module._default.Same0$T), $initHeapForallStmt#0) && Seq#Length($ih#pat0#0) <= Seq#Length($ih#a0#0) && Seq#SameUntil($ih#pat0#0, $ih#a0#0, Seq#Length($ih#pat0#0)) && (Seq#Rank($ih#pat0#0) < Seq#Rank(pat#0) || (Seq#Rank($ih#pat0#0) == Seq#Rank(pat#0) && Seq#Rank($ih#a0#0) < Seq#Rank(a#0))) ==> _module.__default.IsRelaxedPrefixAux(_module._default.Same0$T, $LS($LZ), $Heap, $ih#pat0#0, $ih#a0#0, LitInt(1)))'
      // TRIG (forall $ih#m0#0: DatatypeType, $ih#n0#0: DatatypeType :: $Is($ih#m0#0, Tclass._module.Nat()) && $IsAlloc($ih#m0#0, Tclass._module.Nat(), $initHeapForallStmt#0) && $Is($ih#n0#0, Tclass._module.Nat()) && $IsAlloc($ih#n0#0, Tclass._module.Nat(), $initHeapForallStmt#0) && Lit(true) && (DtRank($ih#m0#0) < DtRank(m#0) || (DtRank($ih#m0#0) == DtRank(m#0) && DtRank($ih#n0#0) < DtRank(n#0))) ==> _module.__default.mult($LS($LZ), $Heap, $ih#m0#0, _module.__default.plus($LS($LZ), $Heap, $ih#n0#0, $ih#n0#0)) == _module.__default.mult($LS($LZ), $Heap, _module.__default.plus($LS($LZ), $Heap, $ih#m0#0, $ih#m0#0), $ih#n0#0))
      var qq = new Bpl.ForallExpr(tok, bvars, tr, BplImp(ante, post));  // TODO: Add a SMART_TRIGGER here.  If we can't find one, abort the attempt to do induction automatically
      exporter.Add(TrAssumeCmd(tok, qq));
    }
  }

  void TrForallAssign(ForallStmt s, SingleAssignStmt s0,
    BoogieStmtListBuilder definedness, BoogieStmtListBuilder updater, Variables locals, ExpressionTranslator etran) {
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
    //       assume (forall o: ref, F: Field ::
    //         { $Heap[o,F] }
    //         $Heap[o,F] = oldHeap[o,F] ||
    //         (exists x,y :: Range(x,y) && o == E(x,y) && F = f));
    //       assume (forall x,y ::  Range ==> $Heap[ E[$Heap:=oldHeap], F] == G[$Heap:=oldHeap]); (**)
    //     (b)
    //       assume (forall o: ref, F: Field ::
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
    string description = GetObjFieldDetails(lhs, etran, out var obj, out var F);
    var (lhsObj, lhsField) = lhs switch {
      MemberSelectExpr e => (e.Obj, e.Member as Field),
      SeqSelectExpr e => (e.Seq, null),
      MultiSelectExpr e => (e.Array, null),
      _ => throw new cce.UnreachableException()
    };
    var desc = new Modifiable(description, GetContextModifiesFrames(), lhsObj, lhsField);
    definedness.Add(Assert(lhs.tok, Bpl.Expr.SelectTok(lhs.tok, etran.ModifiesFrame(lhs.tok), obj, F),
      desc, definedness.Context));
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
      CheckSubrange(r.Tok, translatedRhs, rhs.Type, lhsType, rhs, definedness);
      if (lhs is MemberSelectExpr) {
        var fse = (MemberSelectExpr)lhs;
        Contract.Assert(lhsField != null);
        Check_NewRestrictions(fse.tok, fse.Obj, obj, lhsField, translatedRhs, definedness, etran);
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
      GetObjFieldDetails(lhsPrime, etran, out var objPrime, out var FPrime);
      var Rhs = ((ExprRhs)s0.Rhs).Expr;
      var rhs = etran.TrExpr(Substitute(Rhs, null, substMap));
      var rhsPrime = etran.TrExpr(Substitute(Rhs, null, substMapPrime));
      var lhsComponents = new List<Expression> { lhsObj };
      if (lhs is SeqSelectExpr sse) {
        lhsComponents.Add(sse.E0);
      } else if (lhs is MultiSelectExpr multi) {
        lhsComponents.AddRange(multi.Indices);
      }

      definedness.Add(Assert(s0.Tok,
        BplOr(
          BplOr(Bpl.Expr.Neq(obj, objPrime), Bpl.Expr.Neq(F, FPrime)),
          Bpl.Expr.Eq(rhs, rhsPrime)),
        new ForallLHSUnique(s.BoundVars, s.Range, lhsComponents, Rhs), definedness.Context));
    }

    definedness.Add(TrAssumeCmd(s.Tok, Bpl.Expr.False));

    // Now for the translation of the update itself

    Bpl.IdentifierExpr prevHeap = GetPrevHeapVar_IdExpr(s.Tok, locals);
    var prevEtran = new ExpressionTranslator(this, predef, prevHeap, etran.scope);
    updater.Add(Bpl.Cmd.SimpleAssign(s.Tok, prevHeap, etran.HeapExpr));
    updater.Add(new Bpl.HavocCmd(s.Tok, new List<Bpl.IdentifierExpr> { etran.HeapCastToIdentifierExpr }));
    updater.Add(TrAssumeCmd(s.Tok, HeapSucc(prevHeap, etran.HeapExpr)));

    // Here comes:
    //   assume (forall o: ref, f: Field ::
    //     { $Heap[o,f] }
    //     $Heap[o,f] = oldHeap[o,f] ||
    //     (exists x,y :: Range(x,y)[$Heap:=oldHeap] &&
    //                    o == Object(x,y)[$Heap:=oldHeap] && f == Field(x,y)[$Heap:=oldHeap]));
    Bpl.BoundVariable oVar = new Bpl.BoundVariable(s.Tok, new Bpl.TypedIdent(s.Tok, "$o", predef.RefType));
    Bpl.IdentifierExpr o = new Bpl.IdentifierExpr(s.Tok, oVar);
    Bpl.BoundVariable fVar = new Bpl.BoundVariable(s.Tok, new Bpl.TypedIdent(s.Tok, "$f", predef.FieldName(s.Tok)));
    Bpl.IdentifierExpr f = new Bpl.IdentifierExpr(s.Tok, fVar);
    Bpl.Expr heapOF = ReadHeap(s.Tok, etran.HeapExpr, o, f);
    Bpl.Expr oldHeapOF = ReadHeap(s.Tok, prevHeap, o, f);
    List<bool> freeOfAlloc = BoundedPool.HasBounds(s.Bounds, BoundedPool.PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc);
    List<Variable> xBvars = new List<Variable>();
    var xBody = etran.TrBoundVariables(s.BoundVars, xBvars, false, freeOfAlloc);
    xBody = BplAnd(xBody, prevEtran.TrExpr(s.Range));
    GetObjFieldDetails(s0.Lhs.Resolved, prevEtran, out var xObj, out var xField);
    xBody = BplAnd(xBody, Bpl.Expr.Eq(o, xObj));
    xBody = BplAnd(xBody, Bpl.Expr.Eq(f, xField));
    //TRIG (exists k#2: int :: (k#2 == LitInt(0 - 3) || k#2 == LitInt(4)) && $o == read($prevHeap, this, _module.MyClass.arr) && $f == MultiIndexField(IndexField(i#0), j#0))
    Bpl.Expr xObjField = new Bpl.ExistsExpr(s.Tok, xBvars, xBody);  // LL_TRIGGER
    Bpl.Expr body = BplOr(Bpl.Expr.Eq(heapOF, oldHeapOF), xObjField);
    var tr = new Trigger(s.Tok, true, new List<Expr>() { heapOF });
    Bpl.Expr qq = new Bpl.ForallExpr(s.Tok, new List<TypeVariable> { }, new List<Variable> { oVar, fVar }, null, tr, body);
    updater.Add(TrAssumeCmd(s.Tok, qq));

    if (s.EffectiveEnsuresClauses != null) {
      foreach (ForallExpr expr in s.EffectiveEnsuresClauses) {
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
  private Bpl.Expr TrForall_NewValueAssumption(IToken tok, List<BoundVar> boundVars, List<BoundedPool> bounds, Expression range, Expression lhs, Expression rhs, Attributes attributes, ExpressionTranslator etran, ExpressionTranslator prevEtran) {
    Contract.Requires(tok != null);
    Contract.Requires(boundVars != null);
    Contract.Requires(bounds != null);
    Contract.Requires(range != null);
    Contract.Requires(lhs != null);
    Contract.Requires(rhs != null);
    Contract.Requires(etran != null);
    Contract.Requires(prevEtran != null);

    List<bool> freeOfAlloc = BoundedPool.HasBounds(bounds, BoundedPool.PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc);
    var xBvars = new List<Variable>();
    Bpl.Expr xAnte = etran.TrBoundVariables(boundVars, xBvars, false, freeOfAlloc);
    xAnte = BplAnd(xAnte, prevEtran.TrExpr(range));
    var g = prevEtran.TrExpr(rhs);
    GetObjFieldDetails(lhs, prevEtran, out var obj, out var field);
    var xHeapOF = ReadHeap(tok, etran.HeapExpr, obj, field);

    g = BoxIfNotNormallyBoxed(rhs.tok, g, rhs.Type);

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
    return new Bpl.ForallExpr(tok, xBvars, tr, BplImp(xAnte, Bpl.Expr.Eq(xHeapOF, g)));
  }

  IEnumerable<Statement> TransitiveSubstatements(Statement s) {
    yield return s;
    foreach (var ss in s.SubStatements.SelectMany(TransitiveSubstatements)) {
      yield return ss;
    }
  }

  void TrForallProof(ForallStmt forallStmt, BoogieStmtListBuilder definedness, BoogieStmtListBuilder exporter,
    Variables locals, ExpressionTranslator etran) {
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

    if (forallStmt.BoundVars.Count != 0) {
      // Note, it would be nicer (and arguably more appropriate) to do a SetupBoundVarsAsLocals
      // here (rather than a TrBoundVariables).  However, there is currently no way to apply
      // a substMap to a statement (in particular, to s.Body), so that doesn't work here.
      List<bool> freeOfAlloc = BoundedPool.HasBounds(forallStmt.Bounds, BoundedPool.PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc);

      var bVars = new List<Variable>();
      var typeAntecedent = etran.TrBoundVariables(forallStmt.BoundVars, bVars, true, freeOfAlloc);
      locals.AddRange(bVars);
      var havocIds = new List<Bpl.IdentifierExpr>();
      foreach (Bpl.Variable bv in bVars) {
        havocIds.Add(new Bpl.IdentifierExpr(forallStmt.Tok, bv));
      }
      definedness.Add(new Bpl.HavocCmd(forallStmt.Tok, havocIds));
      definedness.Add(TrAssumeCmd(forallStmt.Tok, typeAntecedent));
    }
    TrStmt_CheckWellformed(forallStmt.Range, definedness, locals, etran, false);
    definedness.Add(TrAssumeCmdWithDependencies(etran, forallStmt.Range.tok, forallStmt.Range, "forall statement range"));

    var ensuresDefinedness = new BoogieStmtListBuilder(this, options, definedness.Context);
    foreach (var ens in forallStmt.Ens) {
      TrStmt_CheckWellformed(ens.E, ensuresDefinedness, locals, etran, false);
      ensuresDefinedness.Add(TrAssumeCmdWithDependencies(etran, ens.E.tok, ens.E, "forall statement ensures clause"));
    }
    PathAsideBlock(forallStmt.Tok, ensuresDefinedness, definedness);

    if (forallStmt.Body != null) {
      TrStmt(forallStmt.Body, definedness, locals, etran);

      // check that postconditions hold
      foreach (var ens in forallStmt.Ens) {
        foreach (var split in TrSplitExpr(definedness.Context, ens.E, etran, true, out var splitHappened)) {
          if (split.IsChecked) {
            definedness.Add(Assert(split.Tok, split.E, new ForallPostcondition(ens.E), definedness.Context));
          }
        }
      }
    }

    definedness.Add(TrAssumeCmd(forallStmt.Tok, Bpl.Expr.False));

    // Now for the other branch, where the ensures clauses are exported.
    // If the forall body has side effect such as call to a reveal function,
    // it needs to be exported too.
    var se = forallStmt.Body == null ? Bpl.Expr.True : TrFunctionSideEffect(forallStmt.Body, etran);
    var substMap = new Dictionary<IVariable, Expression>();
    var p = Substitute(forallStmt.EffectiveEnsuresClauses[0], null, substMap);
    var qq = etran.TrExpr(p);
    if (forallStmt.BoundVars.Count != 0) {
      exporter.Add(TrAssumeCmd(forallStmt.Tok, BplAnd(se, qq)));
    } else {
      exporter.Add(TrAssumeCmd(forallStmt.Tok, BplAnd(se, ((Bpl.ForallExpr)qq).Body)));
    }
  }
}