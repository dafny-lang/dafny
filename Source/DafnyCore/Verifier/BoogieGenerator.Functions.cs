using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using DafnyCore.Verifier;
using Microsoft.Boogie;
using static Microsoft.Dafny.Util;
using Bpl = Microsoft.Boogie;
using PODesc = Microsoft.Dafny.ProofObligationDescription;
using static Microsoft.Dafny.GenericErrors;

namespace Microsoft.Dafny;

public partial class BoogieGenerator {

  void AddWellformednessCheck(Function f) {
    Contract.Requires(f != null);
    Contract.Requires(sink != null && predef != null);
    Contract.Requires(f.EnclosingClass != null);
    Contract.Requires(currentModule == null && codeContext == null && isAllocContext != null);
    Contract.Ensures(currentModule == null && codeContext == null && isAllocContext != null);

    Contract.Assert(InVerificationScope(f));

    proofDependencies.SetCurrentDefinition(MethodVerboseName(f.FullDafnyName, MethodTranslationKind.SpecWellformedness));
    currentModule = f.EnclosingClass.EnclosingModuleDefinition;
    codeContext = f;

    Bpl.Expr prevHeap = null;
    Bpl.Expr currHeap = null;
    var ordinaryEtran = new ExpressionTranslator(this, predef, f.tok);
    ExpressionTranslator etran;
    var inParams_Heap = new List<Bpl.Variable>();
    if (f is TwoStateFunction) {
      var prevHeapVar = new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, "previous$Heap", predef.HeapType), true);
      var currHeapVar = new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, "current$Heap", predef.HeapType), true);
      inParams_Heap.Add(prevHeapVar);
      inParams_Heap.Add(currHeapVar);
      prevHeap = new Bpl.IdentifierExpr(f.tok, prevHeapVar);
      currHeap = new Bpl.IdentifierExpr(f.tok, currHeapVar);
      etran = new ExpressionTranslator(this, predef, currHeap, prevHeap);
    } else {
      etran = ordinaryEtran;
    }

    // parameters of the procedure
    var typeInParams = MkTyParamFormals(GetTypeParams(f), true);
    var inParams = new List<Bpl.Variable>();
    var outParams = new List<Bpl.Variable>();
    if (!f.IsStatic) {
      var th = new Bpl.IdentifierExpr(f.tok, "this", TrReceiverType(f));
      Bpl.Expr wh = Bpl.Expr.And(
        ReceiverNotNull(th),
        (f is TwoStateFunction ? etran.Old : etran).GoodRef(f.tok, th, ModuleResolver.GetReceiverType(f.tok, f)));
      Bpl.Formal thVar = new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, "this", TrReceiverType(f), wh), true);
      inParams.Add(thVar);
    }
    foreach (Formal p in f.Formals) {
      Bpl.Type varType = TrType(p.Type);
      Bpl.Expr wh = GetWhereClause(p.tok, new Bpl.IdentifierExpr(p.tok, p.AssignUniqueName(f.IdGenerator), varType), p.Type,
        p.IsOld ? etran.Old : etran, f is TwoStateFunction ? ISALLOC : NOALLOC);
      inParams.Add(new Bpl.Formal(p.tok, new Bpl.TypedIdent(p.tok, p.AssignUniqueName(f.IdGenerator), varType, wh), true));
    }
    if (f.Result != null) {
      Formal p = f.Result;
      Contract.Assert(!p.IsOld);
      Bpl.Type varType = TrType(p.Type);
      Bpl.Expr wh = GetWhereClause(p.tok, new Bpl.IdentifierExpr(p.tok, p.AssignUniqueName(f.IdGenerator), varType), p.Type, etran, NOALLOC);
      outParams.Add(new Bpl.Formal(p.tok, new Bpl.TypedIdent(p.tok, p.AssignUniqueName(f.IdGenerator), varType, wh), true));
    }
    // the procedure itself
    var req = new List<Bpl.Requires>();
    // free requires mh == ModuleContextHeight && fh == FunctionContextHeight;
    req.Add(Requires(f.tok, true, etran.HeightContext(f), null, null, null));
    if (f is TwoStateFunction) {
      // free requires prevHeap == Heap && HeapSucc(prevHeap, currHeap) && IsHeap(currHeap)
      var a0 = Bpl.Expr.Eq(prevHeap, ordinaryEtran.HeapExpr);
      var a1 = HeapSucc(prevHeap, currHeap);
      var a2 = FunctionCall(f.tok, BuiltinFunction.IsGoodHeap, null, currHeap);
      req.Add(Requires(f.tok, true, BplAnd(a0, BplAnd(a1, a2)), null, null, null));
    }

    // modifies $Heap
    var mod = new List<Bpl.IdentifierExpr> {
      ordinaryEtran.HeapCastToIdentifierExpr,
    };
    // check that postconditions hold
    var ens = new List<Bpl.Ensures>();
    foreach (AttributedExpression p in f.Ens) {
      var functionHeight = currentModule.CallGraph.GetSCCRepresentativePredecessorCount(f);
      var splits = new List<SplitExprInfo>();
      bool splitHappened /*we actually don't care*/ = TrSplitExpr(p.E, splits, true, functionHeight, true, true, etran);
      var (errorMessage, successMessage) = CustomErrorMessage(p.Attributes);
      foreach (var s in splits) {
        if (s.IsChecked && !RefinementToken.IsInherited(s.Tok, currentModule)) {
          AddEnsures(ens, EnsuresWithDependencies(s.Tok, false, p.E, s.E, errorMessage, successMessage, null));
        }
      }
    }
    var proc = new Bpl.Procedure(f.tok, "CheckWellformed" + NameSeparator + f.FullSanitizedName, new List<Bpl.TypeVariable>(),
      Concat(Concat(typeInParams, inParams_Heap), inParams), outParams,
      false, req, mod, ens, etran.TrAttributes(f.Attributes, null));
    AddVerboseNameAttribute(proc, f.FullDafnyName, MethodTranslationKind.SpecWellformedness);
    sink.AddTopLevelDeclaration(proc);

    if (InsertChecksums) {
      InsertChecksum(f, proc, true);
    }

    Contract.Assert(proc.InParams.Count == typeInParams.Count + inParams_Heap.Count + inParams.Count);
    // Changed the next line to strip from inParams instead of proc.InParams
    // They should be the same, but hence the added contract
    var implInParams = Bpl.Formal.StripWhereClauses(inParams);
    var implOutParams = Bpl.Formal.StripWhereClauses(outParams);
    var locals = new List<Variable>();
    var builder = new BoogieStmtListBuilder(this, options);
    var builderInitializationArea = new BoogieStmtListBuilder(this, options);
    builder.Add(new CommentCmd("AddWellformednessCheck for function " + f));
    if (f is TwoStateFunction) {
      // $Heap := current$Heap;
      var heap = ordinaryEtran.HeapCastToIdentifierExpr;
      builder.Add(Bpl.Cmd.SimpleAssign(f.tok, heap, etran.HeapExpr));
      etran = ordinaryEtran;  // we no longer need the special heap names
    }
    builder.AddCaptureState(f.tok, false, "initial state");

    DefineFrame(f.tok, etran.ReadsFrame(f.tok), f.Reads.Expressions, builder, locals, null);
    InitializeFuelConstant(f.tok, builder, etran);

    var delayer = new ReadsCheckDelayer(etran, null, locals, builderInitializationArea, builder);

    // Check well-formedness of any default-value expressions (before assuming preconditions).
    delayer.DoWithDelayedReadsChecks(true, wfo => {
      foreach (var formal in f.Formals.Where(formal => formal.DefaultValue != null)) {
        var e = formal.DefaultValue;
        CheckWellformed(e, wfo, locals, builder, etran);
        builder.Add(new Bpl.AssumeCmd(e.tok, etran.CanCallAssumption(e)));
        CheckSubrange(e.tok, etran.TrExpr(e), e.Type, formal.Type, builder);

        if (formal.IsOld) {
          Bpl.Expr wh = GetWhereClause(e.tok, etran.TrExpr(e), e.Type, etran.Old, ISALLOC, true);
          if (wh != null) {
            var desc = new PODesc.IsAllocated("default value", "in the two-state function's previous state");
            builder.Add(Assert(GetToken(e), wh, desc));
          }
        }
      }
    });

    // Check well-formedness of the preconditions (including termination), and then
    // assume each one of them.  After all that (in particular, after assuming all
    // of them), do the postponed reads checks.
    delayer.DoWithDelayedReadsChecks(false, wfo => {
      foreach (AttributedExpression p in f.Req) {
        if (p.Label != null) {
          p.Label.E = (f is TwoStateFunction ? ordinaryEtran : etran.Old).TrExpr(p.E);
          CheckWellformed(p.E, wfo, locals, builder, etran);
        } else {
          CheckWellformedAndAssume(p.E, wfo, locals, builder, etran, "requires clause");
        }
      }
    });

    // Check well-formedness of the reads clause.  Note that this is done after assuming
    // the preconditions.  In other words, the well-formedness of the reads clause is
    // allowed to assume the precondition (yet, the requires clause is checked to
    // read only those things indicated in the reads clause).
    delayer.DoWithDelayedReadsChecks(false, wfo => {
      CheckFrameWellFormed(wfo, f.Reads.Expressions, locals, builder, etran);
    });

    // If the function is marked as {:concurrent}, check that the reads clause is empty.
    if (Attributes.Contains(f.Attributes, Attributes.ConcurrentAttributeName)) {
      var desc = new PODesc.ConcurrentFrameEmpty("reads clause");
      CheckFrameEmpty(f.tok, etran, etran.ReadsFrame(f.tok), builder, desc, null);
    }

    // check well-formedness of the decreases clauses (including termination, but no reads checks)
    foreach (Expression p in f.Decreases.Expressions) {
      CheckWellformed(p, new WFOptions(null, false), locals, builder, etran);
    }
    // Generate:
    //   if (*) {
    //     check well-formedness of postcondition
    //     assume false;  // don't go on to check the postconditions
    //   } else {
    //     check well-formedness of body
    //     // fall through to check the postconditions themselves
    //   }
    // Here go the postconditions (termination checks included, but no reads checks)
    BoogieStmtListBuilder postCheckBuilder = new BoogieStmtListBuilder(this, options);
    // Assume the type returned by the call itself respects its type (this matters if the type is "nat", for example)
    {
      var args = new List<Bpl.Expr>();
      foreach (var p in GetTypeParams(f)) {
        args.Add(TrTypeParameter(p));
      }
      if (f.IsFuelAware()) {
        args.Add(etran.layerInterCluster.GetFunctionFuel(f));
      }

      if (f.IsOpaque || f.IsMadeImplicitlyOpaque(options)) {
        args.Add(GetRevealConstant(f));
      }
      if (f is TwoStateFunction) {
        args.Add(etran.Old.HeapExpr);
      }
      if (f.ReadsHeap) {
        args.Add(etran.HeapExpr);
      }
      if (!f.IsStatic) {
        args.Add(new Bpl.IdentifierExpr(f.tok, etran.This));
      }
      foreach (var p in f.Formals) {
        args.Add(new Bpl.IdentifierExpr(p.tok, p.AssignUniqueName(f.IdGenerator), TrType(p.Type)));
      }
      Bpl.IdentifierExpr funcID = new Bpl.IdentifierExpr(f.tok, f.FullSanitizedName, TrType(f.ResultType));
      Bpl.Expr funcAppl = new Bpl.NAryExpr(f.tok, new Bpl.FunctionCall(funcID), args);

      var wh = GetWhereClause(f.tok, funcAppl, f.ResultType, etran, NOALLOC);
      if (wh != null) {
        postCheckBuilder.Add(TrAssumeCmd(f.tok, wh));
      }
    }
    // Now for the ensures clauses
    foreach (AttributedExpression p in f.Ens) {
      // assume the postcondition for the benefit of checking the remaining postconditions
      CheckWellformedAndAssume(p.E, new WFOptions(f, false), locals, postCheckBuilder, etran, "ensures clause");
    }
    // Here goes the body (and include both termination checks and reads checks)
    BoogieStmtListBuilder bodyCheckBuilder = new BoogieStmtListBuilder(this, options);
    if (f.Body == null || !RevealedInScope(f)) {
      // don't fall through to postcondition checks
      bodyCheckBuilder.Add(TrAssumeCmd(f.tok, Bpl.Expr.False));
    } else {
      var funcID = new Bpl.FunctionCall(new Bpl.IdentifierExpr(f.tok, f.FullSanitizedName, TrType(f.ResultType)));
      var args = new List<Bpl.Expr>();
      foreach (var p in GetTypeParams(f)) {
        args.Add(TrTypeParameter(p));
      }
      if (f.IsFuelAware()) {
        args.Add(etran.layerInterCluster.GetFunctionFuel(f));
      }

      if (f.IsOpaque || f.IsMadeImplicitlyOpaque(options)) {
        args.Add(GetRevealConstant(f));
      }
      if (f is TwoStateFunction) {
        args.Add(etran.Old.HeapExpr);
      }
      if (f.ReadsHeap) {
        args.Add(etran.HeapExpr);
      }
      foreach (Variable p in implInParams) {
        args.Add(new Bpl.IdentifierExpr(f.tok, p));
      }
      Bpl.Expr funcAppl = new Bpl.NAryExpr(f.tok, funcID, args);

      var bodyCheckDelayer = new ReadsCheckDelayer(etran, null, locals, builderInitializationArea, bodyCheckBuilder);
      bodyCheckDelayer.DoWithDelayedReadsChecks(false, wfo => {
        CheckWellformedWithResult(f.Body, wfo, funcAppl, f.ResultType, locals, bodyCheckBuilder, etran, "function call result");
        if (f.Result != null) {
          var cmd = TrAssumeCmd(f.tok, Bpl.Expr.Eq(funcAppl, TrVar(f.tok, f.Result)));
          proofDependencies?.AddProofDependencyId(cmd, f.tok, new FunctionDefinitionDependency(f));
          bodyCheckBuilder.Add(cmd);
        }
      });

      // Enforce 'older' conditions
      var (olderParameterCount, olderCondition) = OlderCondition(f, funcAppl, implInParams);
      if (olderParameterCount != 0) {
        bodyCheckBuilder.Add(Assert(f.tok, olderCondition, new PODesc.IsOlderProofObligation(olderParameterCount, f.Formals.Count + (f.IsStatic ? 0 : 1))));
      }
    }
    // Combine the two, letting the postcondition be checked on after the "bodyCheckBuilder" branch
    postCheckBuilder.Add(TrAssumeCmd(f.tok, Bpl.Expr.False));
    builder.Add(new Bpl.IfCmd(f.tok, null, postCheckBuilder.Collect(f.tok), null, bodyCheckBuilder.Collect(f.tok)));

    var s0 = builderInitializationArea.Collect(f.tok);
    var s1 = builder.Collect(f.tok);
    var implBody = new StmtList(new List<BigBlock>(s0.BigBlocks.Concat(s1.BigBlocks)), f.tok);

    if (EmitImplementation(f.Attributes)) {
      // emit the impl only when there are proof obligations.
      QKeyValue kv = etran.TrAttributes(f.Attributes, null);
      var impl = AddImplementationWithAttributes(GetToken(f), proc,
        Concat(Concat(Bpl.Formal.StripWhereClauses(typeInParams), inParams_Heap), implInParams),
        implOutParams,
        locals, implBody, kv);
      if (InsertChecksums) {
        InsertChecksum(f, impl);
      }
    }

    Contract.Assert(currentModule == f.EnclosingClass.EnclosingModuleDefinition);
    Contract.Assert(codeContext == f);
    Reset();
  }

  void AddFunctionAxiom(Bpl.Function boogieFunction, Function f, Expression body) {
    Contract.Requires(f != null);
    Contract.Requires(body != null);

    var ax = GetFunctionAxiom(f, body, null);
    AddOtherDefinition(boogieFunction, ax);
    // TODO(namin) Is checking f.Reads.Count==0 excluding Valid() of BinaryTree in the right way?
    //             I don't see how this in the decreasing clause would help there.
    if (!(f is ExtremePredicate) && f.CoClusterTarget == Function.CoCallClusterInvolvement.None && f.Reads.Expressions.Count == 0) {
      var FVs = new HashSet<IVariable>();
      Type usesThis = null;
      bool dontCare0 = false, dontCare1 = false;
      var dontCareHeapAt = new HashSet<Label>();
      foreach (var e in f.Decreases.Expressions) {
        FreeVariablesUtil.ComputeFreeVariables(options, e, FVs, ref dontCare0, ref dontCare1, dontCareHeapAt, ref usesThis, false);
      }

      var allFormals = new List<Formal>();
      var decs = new List<Formal>();
      if (f.IsStatic) {
        Contract.Assert(usesThis == null);
      } else {
        var surrogate = new ThisSurrogate(f.tok, ModuleResolver.GetReceiverType(f.tok, f));
        allFormals.Add(surrogate);
        if (usesThis != null) {
          decs.Add(surrogate);
        }
      }
      foreach (var formal in f.Formals) {
        allFormals.Add(formal);
        if (FVs.Contains(formal)) {
          decs.Add(formal);
        }
      }

      Contract.Assert(decs.Count <= allFormals.Count);
      if (0 < decs.Count && decs.Count < allFormals.Count) {
        var decreasesAxiom = GetFunctionAxiom(f, body, decs);
        AddOtherDefinition(boogieFunction, decreasesAxiom);
      }

      var formalsAxiom = GetFunctionAxiom(f, body, allFormals);
      AddOtherDefinition(boogieFunction, formalsAxiom);
    }
  }

  void AddFunctionConsequenceAxiom(Boogie.Function boogieFunction, Function f, List<AttributedExpression> ens) {
    Contract.Requires(f != null);
    Contract.Requires(predef != null);
    Contract.Requires(f.EnclosingClass != null);

    bool readsHeap = f.ReadsHeap;
    foreach (AttributedExpression e in f.Req.Concat(ens)) {
      readsHeap = readsHeap || UsesHeap(e.E);
    }

    ExpressionTranslator etranHeap;
    ExpressionTranslator etran;
    Bpl.BoundVariable bvPrevHeap = null;
    if (f is TwoStateFunction) {
      bvPrevHeap = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "$prevHeap", predef.HeapType));
      etran = new ExpressionTranslator(this, predef,
        f.ReadsHeap ? new Bpl.IdentifierExpr(f.tok, predef.HeapVarName, predef.HeapType) : null,
        new Bpl.IdentifierExpr(f.tok, bvPrevHeap));
      etranHeap = etran;
    } else {
      etranHeap = new ExpressionTranslator(this, predef, f.tok);
      etran = readsHeap ? etranHeap : new ExpressionTranslator(this, predef, (Bpl.Expr)null);
    }

    // This method generate the Consequence Axiom, which has information about the function's
    // return type and postconditions
    //
    // axiom  // consequence axiom
    //   AXIOM_ACTIVATION
    //   ==>
    //   (forall s, $Heap, formals ::                  // let args := $Heap,formals
    //       { f(s, args) }
    //       f#canCall(args) || USE_VIA_CONTEXT
    //       ==>
    //       ens &&
    //       OlderCondition &&
    //       f(s, args)-has-the-expected type);
    //
    // where:
    //
    // AXIOM_ACTIVATION
    // means:
    //   fh <= FunctionContextHeight
    //
    // USE_VIA_CONTEXT
    //   fh < FunctionContextHeight &&
    //   GOOD_PARAMETERS
    // where GOOD_PARAMETERS means:
    //   $IsGoodHeap($Heap) && this != null && formals-have-the-expected-types &&
    //   Pre($Heap,formals)
    //
    // OlderCondition is added if the function has some 'older' parameters.
    //
    // Note, an antecedent $Heap[this,alloc] is intentionally left out:  including it would only weaken
    // the axiom.  Moreover, leaving it out does not introduce any soundness problem, because the Dafny
    // allocation statement changes only an allocation bit and then re-assumes $IsGoodHeap; so if it is
    // sound after that, then it would also have been sound just before the allocation.
    //
    List<Bpl.Expr> tyargs;
    var formals = MkTyParamBinders(GetTypeParams(f), out tyargs);
    var args = new List<Bpl.Expr>();
    var olderInParams = new List<Bpl.Variable>(); // for use with older-condition
    Bpl.BoundVariable layer;
    if (f.IsFuelAware()) {
      layer = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "$ly", predef.LayerType));
      formals.Add(layer);
      etran = etran.WithCustomFuelSetting(new CustomFuelSettings { { f, new FuelSetting(this, 0, new Bpl.IdentifierExpr(f.tok, layer)) } });
      //etran = etran.WithLayer(new Bpl.IdentifierExpr(f.tok, layer));
      // Note, "layer" is not added to "args" here; rather, that's done below, as needed
    } else {
      layer = null;
    }

    Bpl.BoundVariable reveal;
    if (f.IsOpaque || f.IsMadeImplicitlyOpaque(options)) {
      reveal = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "$reveal", Boogie.Type.Bool));
      formals.Add(reveal);
    } else {
      reveal = null;
    }

    Bpl.Expr ante = Bpl.Expr.True;
    Bpl.Expr anteIsAlloc = Bpl.Expr.True;
    if (f is TwoStateFunction) {
      Contract.Assert(bvPrevHeap != null);
      formals.Add(bvPrevHeap);
      args.Add(etran.Old.HeapExpr);
      // ante:  $IsGoodHeap($prevHeap) &&
      var goodHeap = FunctionCall(f.tok, BuiltinFunction.IsGoodHeap, null, etran.Old.HeapExpr);
      ante = BplAnd(ante, goodHeap);
      anteIsAlloc = BplAnd(anteIsAlloc, goodHeap);
    }
    var bvHeap = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, predef.HeapVarName, predef.HeapType));
    if (f.ReadsHeap) {
      args.Add(new Bpl.IdentifierExpr(f.tok, bvHeap));
    }
    // ante:  $IsGoodHeap($Heap) && $HeapSucc($prevHeap, $Heap) && this != null && formals-have-the-expected-types &&
    if (readsHeap) {
      Bpl.Expr goodHeap = FunctionCall(f.tok, BuiltinFunction.IsGoodHeap, null, etranHeap.HeapExpr);
      formals.Add(bvHeap);
      ante = BplAnd(ante, goodHeap);
      anteIsAlloc = BplAnd(anteIsAlloc, f.ReadsHeap ? goodHeap : Bpl.Expr.True);
      if (f is TwoStateFunction) {
        var heapSucc = HeapSucc(etran.Old.HeapExpr, etran.HeapExpr);
        ante = BplAnd(ante, heapSucc);
        anteIsAlloc = BplAnd(anteIsAlloc, f.ReadsHeap ? heapSucc : Bpl.Expr.True);
      }
    }

    if (!f.IsStatic) {
      var bvThis = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, etran.This, TrReceiverType(f)));
      formals.Add(bvThis);
      olderInParams.Add(bvThis);
      var bvThisIdExpr = new Bpl.IdentifierExpr(f.tok, bvThis);
      args.Add(bvThisIdExpr);
      // add well-typedness conjunct to antecedent
      Type thisType = ModuleResolver.GetReceiverType(f.tok, f);
      Bpl.Expr wh = Bpl.Expr.And(
        ReceiverNotNull(bvThisIdExpr),
        (f is TwoStateFunction ? etran.Old : etran).GoodRef(f.tok, bvThisIdExpr, thisType));
      ante = BplAnd(ante, wh);
      anteIsAlloc = BplAnd(anteIsAlloc, ReceiverNotNull(bvThisIdExpr));
      wh = GetWhereClause(f.tok, bvThisIdExpr, thisType, f is TwoStateFunction ? etranHeap.Old : etranHeap, ISALLOC, true);
      if (wh != null) {
        anteIsAlloc = BplAnd(anteIsAlloc, wh);
      }
    }
    foreach (Formal p in f.Formals) {
      var bv = new Bpl.BoundVariable(p.tok, new Bpl.TypedIdent(p.tok, p.AssignUniqueName(currentDeclaration.IdGenerator), TrType(p.Type)));
      Bpl.Expr formal = new Bpl.IdentifierExpr(p.tok, bv);
      formals.Add(bv);
      olderInParams.Add(bv);
      args.Add(formal);
      // add well-typedness conjunct to antecedent
      Bpl.Expr wh = GetWhereClause(p.tok, formal, p.Type, p.IsOld ? etran.Old : etran, NOALLOC);
      if (wh != null) { ante = BplAnd(ante, wh); }
      wh = GetWhereClause(p.tok, formal, p.Type, p.IsOld ? etranHeap.Old : etranHeap, ISALLOC);
      if (wh != null) { anteIsAlloc = BplAnd(anteIsAlloc, wh); }
    }

    Bpl.Expr funcAppl;
    {
      var funcID = new Bpl.IdentifierExpr(f.tok, f.FullSanitizedName, TrType(f.ResultType));
      var funcArgs = new List<Bpl.Expr>();
      funcArgs.AddRange(tyargs);
      /*
      if (f.IsFueled) {
          funcArgs.Add(etran.layerInterCluster.GetFunctionFuel(f));
      } else if (layer != null) {
         var ly = new Bpl.IdentifierExpr(f.tok, layer);
         funcArgs.Add(FunctionCall(f.tok, BuiltinFunction.LayerSucc, null, ly));
      }
       */
      if (layer != null) {
        funcArgs.Add(new Bpl.IdentifierExpr(f.tok, layer));
      }

      if (reveal != null) {
        funcArgs.Add(new Bpl.IdentifierExpr(f.tok, reveal));
      }

      funcArgs.AddRange(args);
      funcAppl = new Bpl.NAryExpr(f.tok, new Bpl.FunctionCall(funcID), funcArgs);
    }

    Bpl.Expr pre = Bpl.Expr.True;
    foreach (AttributedExpression req in f.Req) {
      pre = BplAnd(pre, etran.TrExpr(req.E));
    }
    // useViaContext: fh < FunctionContextHeight
    Expr useViaContext = !(InVerificationScope(f) || (f.EnclosingClass is TraitDecl))
      ? Bpl.Expr.True
      : Bpl.Expr.Lt(Expr.Literal(forModule.CallGraph.GetSCCRepresentativePredecessorCount(f)), etran.FunctionContextHeight());
    // useViaCanCall: f#canCall(args)
    Bpl.IdentifierExpr canCallFuncID = new Bpl.IdentifierExpr(f.tok, f.FullSanitizedName + "#canCall", Bpl.Type.Bool);
    Bpl.Expr useViaCanCall = new Bpl.NAryExpr(f.tok, new Bpl.FunctionCall(canCallFuncID), Concat(tyargs, args));

    // ante := useViaCanCall || (useViaContext && typeAnte && pre)
    ante = Bpl.Expr.Or(useViaCanCall, BplAnd(useViaContext, BplAnd(ante, pre)));
    anteIsAlloc = Bpl.Expr.Or(useViaCanCall, BplAnd(useViaContext, BplAnd(anteIsAlloc, pre)));

    Bpl.Trigger tr = BplTriggerHeap(this, f.tok, funcAppl,
      (f.ReadsHeap || !readsHeap) ? null : etran.HeapExpr);
    Bpl.Expr post = Bpl.Expr.True;
    // substitute function return value with the function call.
    var substMap = new Dictionary<IVariable, Expression>();
    if (f.Result != null) {
      substMap.Add(f.Result, new BoogieWrapper(funcAppl, f.ResultType));
    }
    foreach (AttributedExpression p in ens) {
      Bpl.Expr q = etran.TrExpr(Substitute(p.E, null, substMap));
      post = BplAnd(post, q);
    }
    var (olderParameterCount, olderCondition) = OlderCondition(f, funcAppl, olderInParams);
    if (olderParameterCount != 0) {
      post = BplAnd(post, olderCondition);
    }
    Bpl.Expr whr = GetWhereClause(f.tok, funcAppl, f.ResultType, etran, NOALLOC);
    if (whr != null) { post = Bpl.Expr.And(post, whr); }

    Bpl.Expr ax = BplForall(f.tok, new List<Bpl.TypeVariable>(), formals, null, tr, Bpl.Expr.Imp(ante, post));
    var activate = AxiomActivation(f, etran);
    string comment = "consequence axiom for " + f.FullSanitizedName;
    var consequenceAxiom = new Bpl.Axiom(f.tok, Bpl.Expr.Imp(activate, ax), comment);
    AddOtherDefinition(boogieFunction, consequenceAxiom);

    if (f.ResultType.MayInvolveReferences) {
      whr = GetWhereClause(f.tok, funcAppl, f.ResultType, etranHeap, ISALLOC, true);
      if (whr != null) {
        if (readsHeap) {
          Contract.Assert(formals.Contains(bvHeap));
        } else {
          formals = Util.Cons(bvHeap, formals);
          var goodHeap = FunctionCall(f.tok, BuiltinFunction.IsGoodHeap, null, etranHeap.HeapExpr);
          anteIsAlloc = BplAnd(anteIsAlloc, goodHeap);
        }

        ax = BplForall(f.tok, new List<Bpl.TypeVariable>(), formals, null, BplTrigger(whr), Bpl.Expr.Imp(anteIsAlloc, whr));

        comment = "alloc consequence axiom for " + f.FullSanitizedName;
        var allocConsequenceAxiom = new Bpl.Axiom(f.tok, Bpl.Expr.Imp(activate, ax), comment);
        AddOtherDefinition(boogieFunction, allocConsequenceAxiom);
      }
    }
  }

  /// <summary>
  /// The list of formals "lits" is allowed to contain an object of type ThisSurrogate, which indicates that
  /// the receiver parameter of the function should be included among the lit formals.
  /// </summary>
  private Axiom GetFunctionAxiom(Function f, Expression body, List<Formal> lits) {
    Contract.Requires(f != null);
    Contract.Requires(predef != null);
    Contract.Requires(f.EnclosingClass != null);
    Contract.Ensures((Contract.Result<Axiom>() == null) == (body == null)); // return null iff body is null

    // This method generates the Definition Axiom, suitably modified according to the optional "lits".
    //
    // axiom  // definition axiom
    //   AXIOM_ACTIVATION
    //   ==>
    //   (forall s, $Heap, formals ::                  // let args := $Heap,formals
    //       { f(Succ(s), args) }                      // (*)
    //       (f#canCall(args) || USE_VIA_CONTEXT)
    //       ==>
    //       BODY-can-make-its-calls &&
    //       f(Succ(s), args) == BODY);                // (*)
    //
    // where:
    //
    // AXIOM_ACTIVATION
    // for visibility==ForeignModuleOnly, means:
    //   true
    // for visibility==IntraModuleOnly, means:
    //   fh <= FunctionContextHeight
    //
    // USE_VIA_CONTEXT
    // for visibility==ForeignModuleOnly, means:
    //   GOOD_PARAMETERS
    // for visibility==IntraModuleOnly, means:
    //   fh < FunctionContextHeight &&
    //   GOOD_PARAMETERS
    // where GOOD_PARAMETERS means:
    //   $IsGoodHeap($Heap) && this != null && formals-have-the-expected-types &&
    //   Pre($Heap,formals)
    //
    // NOTE: this is lifted out to a #requires function for intra module calls,
    //       and used in the function pseudo-handles for top level functions.
    //       For body-less functions, this is emitted when body is null.
    //
    // BODY
    // means:
    //   the body of f translated with "s" as the layer argument
    //
    // The variables "formals" are the formals of function "f".
    // The list "args" is the list of formals of function "f".
    //
    // The translation of "body" uses "s" as the layer argument for intra-cluster calls and the default layer argument
    // (which is Succ(0)) for other calls.  Usually, the layer argument in the LHS of the definition (and also in the trigger,
    // see the two occurrences of (*) above) use Succ(s) as the layer argument.  However, if "lits" are specified, then
    // then the argument used is just "s" (in both the LHS and trigger).
    //
    // Note, an antecedent $Heap[this,alloc] is intentionally left out:  including it would only weaken
    // the axiom.  Moreover, leaving it out does not introduce any soundness problem, because the Dafny
    // allocation statement changes only an allocation bit and then re-assumes $IsGoodHeap; so if it is
    // sound after that, then it would also have been sound just before the allocation.
    //

    bool readsHeap = f.ReadsHeap;
    foreach (AttributedExpression e in f.Req) {
      readsHeap = readsHeap || UsesHeap(e.E);
    }

    if (body != null && UsesHeap(body)) {
      readsHeap = true;
    }

    ExpressionTranslator etran;
    Bpl.BoundVariable bvPrevHeap = null;
    if (f is TwoStateFunction) {
      bvPrevHeap = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "$prevHeap", predef.HeapType));
      etran = new ExpressionTranslator(this, predef,
        f.ReadsHeap ? new Bpl.IdentifierExpr(f.tok, predef.HeapVarName, predef.HeapType) : null,
        new Bpl.IdentifierExpr(f.tok, bvPrevHeap));
    } else {
      etran = readsHeap
        ? new ExpressionTranslator(this, predef, f.tok)
        : new ExpressionTranslator(this, predef, (Bpl.Expr)null);
    }

    // quantify over the type arguments, and add them first to the arguments
    List<Bpl.Expr> args = new List<Bpl.Expr>();
    List<Bpl.Expr> tyargs = GetTypeArguments(f, null).ConvertAll(TypeToTy);

    var forallFormals = MkTyParamBinders(GetTypeParams(f), out _);
    var funcFormals = MkTyParamBinders(GetTypeParams(f), out _);
    var reqFuncArguments = new List<Bpl.Expr>(tyargs);

    Bpl.BoundVariable layer;
    Bpl.BoundVariable reveal;
    if (f.IsFuelAware()) {
      layer = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "$ly", predef.LayerType));
      forallFormals.Add(layer);
      funcFormals.Add(layer);
      reqFuncArguments.Add(new Bpl.IdentifierExpr(f.tok, layer));
      // Note, "layer" is not added to "args" here; rather, that's done below, as needed
    } else {
      layer = null;
    }

    if (f.IsOpaque || f.IsMadeImplicitlyOpaque(options)) {
      reveal = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "$reveal", Boogie.Type.Bool));
      //funcFormals.Add(reveal);
      //reqFuncArguments.Add(new Bpl.IdentifierExpr(f.tok, reveal));
      // Note, "reveal" is not added to "args" here; rather, that's done below, as needed
    } else {
      reveal = null;
    }

    Bpl.Expr ante = Bpl.Expr.True;
    if (f is TwoStateFunction) {
      Contract.Assert(bvPrevHeap != null);
      forallFormals.Add(bvPrevHeap);
      funcFormals.Add(bvPrevHeap);
      args.Add(etran.Old.HeapExpr);
      reqFuncArguments.Add(new Bpl.IdentifierExpr(f.tok, bvPrevHeap));
      // ante:  $IsGoodHeap($prevHeap) &&
      ante = BplAnd(ante, FunctionCall(f.tok, BuiltinFunction.IsGoodHeap, null, etran.Old.HeapExpr));
    }

    Bpl.Expr goodHeap = null;
    var bv = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, predef.HeapVarName, predef.HeapType));
    if (f.ReadsHeap) {
      funcFormals.Add(bv);
    }

    if (f.ReadsHeap) {
      args.Add(new Bpl.IdentifierExpr(f.tok, bv));
      reqFuncArguments.Add(new Bpl.IdentifierExpr(f.tok, bv));
    }

    // ante:  $IsGoodHeap($Heap) && $HeapSucc($prevHeap, $Heap) && this != null && formals-have-the-expected-types &&
    if (readsHeap) {
      forallFormals.Add(bv);
      goodHeap = FunctionCall(f.tok, BuiltinFunction.IsGoodHeap, null, etran.HeapExpr);
      ante = BplAnd(ante, goodHeap);
    }

    if (f is TwoStateFunction && f.ReadsHeap) {
      ante = BplAnd(ante, HeapSucc(etran.Old.HeapExpr, etran.HeapExpr));
    }

    Expression receiverReplacement = null;
    if (!f.IsStatic) {
      var bvThis = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, etran.This, TrReceiverType(f)));
      forallFormals.Add(bvThis);
      funcFormals.Add(bvThis);
      reqFuncArguments.Add(new Bpl.IdentifierExpr(f.tok, bvThis));
      var bvThisIdExpr = new Bpl.IdentifierExpr(f.tok, bvThis);
      if (lits != null && lits.Exists(p => p is ThisSurrogate)) {
        args.Add(Lit(bvThisIdExpr));
        var th = new ThisExpr(f);
        var l = new UnaryOpExpr(f.tok, UnaryOpExpr.Opcode.Lit, th) {
          Type = th.Type
        };
        receiverReplacement = l;
      } else {
        args.Add(bvThisIdExpr);
      }

      // add well-typedness conjunct to antecedent
      Type thisType = ModuleResolver.GetReceiverType(f.tok, f);
      Bpl.Expr wh = Bpl.Expr.And(
        ReceiverNotNull(bvThisIdExpr),
        (f is TwoStateFunction ? etran.Old : etran).GoodRef(f.tok, bvThisIdExpr, thisType));
      ante = BplAnd(ante, wh);
    }

    var typeMap = new Dictionary<TypeParameter, Type>();
    var anteReqAxiom = ante; // note that antecedent so far is the same for #requires axioms, even the receiver parameter of a two-state function
    var substMap = new Dictionary<IVariable, Expression>();
    foreach (Formal p in f.Formals) {
      var pType = p.Type.Subst(typeMap);
      bv = new Bpl.BoundVariable(p.tok,
        new Bpl.TypedIdent(p.tok, p.AssignUniqueName(currentDeclaration.IdGenerator), TrType(pType)));
      forallFormals.Add(bv);
      funcFormals.Add(bv);
      reqFuncArguments.Add(new Bpl.IdentifierExpr(f.tok, bv));
      Bpl.Expr formal = new Bpl.IdentifierExpr(p.tok, bv);
      if (lits != null && lits.Contains(p) && !substMap.ContainsKey(p)) {
        args.Add(Lit(formal));
        var ie = new IdentifierExpr(p.tok, p.AssignUniqueName(f.IdGenerator));
        ie.Var = p;
        ie.Type = ie.Var.Type;
        var l = new UnaryOpExpr(p.tok, UnaryOpExpr.Opcode.Lit, ie);
        l.Type = ie.Var.Type;
        substMap.Add(p, l);
      } else {
        args.Add(formal);
      }

      // add well-typedness conjunct to antecedent
      Bpl.Expr wh = GetWhereClause(p.tok, formal, pType, p.IsOld ? etran.Old : etran, NOALLOC);
      if (wh != null) {
        ante = BplAnd(ante, wh);
      }

      wh = GetWhereClause(p.tok, formal, pType, etran, NOALLOC);
      if (wh != null) {
        anteReqAxiom = BplAnd(anteReqAxiom, wh);
      }
    }

    Bpl.Expr pre = Bpl.Expr.True;
    foreach (AttributedExpression req in f.Req) {
      pre = BplAnd(pre, etran.TrExpr(Substitute(req.E, receiverReplacement, substMap)));
    }

    var preReqAxiom = pre;
    if (f is TwoStateFunction) {
      // Checked preconditions that old parameters really existed in previous state
      var index = 0;
      Bpl.Expr preRA = Bpl.Expr.True;
      foreach (var formal in f.Formals) {
        if (formal.IsOld) {
          var dafnyFormalIdExpr = new IdentifierExpr(formal.tok, formal);
          preRA = BplAnd(preRA, MkIsAlloc(etran.TrExpr(dafnyFormalIdExpr), formal.Type, etran.Old.HeapExpr));
        }

        index++;
      }

      preReqAxiom = BplAnd(preRA, pre);
    }

    // Add the precondition function and its axiom (which is equivalent to the anteReqAxiom)
    if (body == null || (RevealedInScope(f) && lits == null)) {
      var precondF = new Bpl.Function(f.tok,
        RequiresName(f), new List<Bpl.TypeVariable>(),
        funcFormals.ConvertAll(v => (Bpl.Variable)BplFormalVar(null, v.TypedIdent.Type, true)),
        BplFormalVar(null, Bpl.Type.Bool, false));
      sink.AddTopLevelDeclaration(precondF);

      var appl = FunctionCall(f.tok, RequiresName(f), Bpl.Type.Bool, reqFuncArguments);
      Bpl.Trigger trig = BplTriggerHeap(this, f.tok, appl, readsHeap ? etran.HeapExpr : null);
      // axiom (forall params :: { f#requires(params) }  ante ==> f#requires(params) == pre);
      AddOtherDefinition(precondF, new Axiom(f.tok,
        BplForall(forallFormals, trig, BplImp(anteReqAxiom, Bpl.Expr.Eq(appl, preReqAxiom))),
        "#requires axiom for " + f.FullSanitizedName));
    }

    if (body == null || !RevealedInScope(f)) {
      return null;
    }

    // useViaContext: fh < FunctionContextHeight
    ModuleDefinition mod = f.EnclosingClass.EnclosingModuleDefinition;
    Bpl.Expr useViaContext = !InVerificationScope(f)
      ? Bpl.Expr.True
      : Bpl.Expr.Lt(Bpl.Expr.Literal(forModule.CallGraph.GetSCCRepresentativePredecessorCount(f)), etran.FunctionContextHeight());
    // ante := (useViaContext && typeAnte && pre)
    ante = BplAnd(useViaContext, BplAnd(ante, pre));

    // useViaCanCall: f#canCall(args)
    Bpl.IdentifierExpr canCallFuncID = new Bpl.IdentifierExpr(f.tok, f.FullSanitizedName + "#canCall", Bpl.Type.Bool);
    Bpl.Expr useViaCanCall = new Bpl.NAryExpr(f.tok, new Bpl.FunctionCall(canCallFuncID), Concat(tyargs, args));

    // ante := useViaCanCall || (useViaContext && typeAnte && pre)
    ante = Bpl.Expr.Or(useViaCanCall, ante);

    Bpl.Expr funcAppl;
    {
      var funcID = new Bpl.IdentifierExpr(f.tok, f.FullSanitizedName, TrType(f.ResultType));
      var funcArgs = new List<Bpl.Expr>();
      funcArgs.AddRange(tyargs);
      if (layer != null) {
        var ly = new Bpl.IdentifierExpr(f.tok, layer);
        //if (lits == null) {
        funcArgs.Add(LayerSucc(ly));
        //} else {
        //  funcArgs.Add(ly);
        //}
      }

      if (reveal != null) {
        funcArgs.Add(new Bpl.LiteralExpr(f.tok, true));
      }

      funcArgs.AddRange(args);
      funcAppl = new Bpl.NAryExpr(f.tok, new Bpl.FunctionCall(funcID), funcArgs);
    }

    Bpl.Trigger tr = BplTriggerHeap(this, f.tok, funcAppl, readsHeap ? etran.HeapExpr : null);
    Bpl.Expr tastyVegetarianOption; // a.k.a. the "meat" of the operation :)
    if (!RevealedInScope(f)) {
      tastyVegetarianOption = Bpl.Expr.True;
    } else {
      var bodyWithSubst = Substitute(body, receiverReplacement, substMap);
      if (f is PrefixPredicate) {
        var pp = (PrefixPredicate)f;
        bodyWithSubst = PrefixSubstitution(pp, bodyWithSubst);
      }

      Bpl.Expr ly = null;
      if (layer != null) {
        ly = new Bpl.IdentifierExpr(f.tok, layer);
        if (lits != null) {
          // Lit axiom doesn't consume any fuel
          ly = LayerSucc(ly);
        }
      }

      var etranBody = layer == null ? etran : etran.LimitedFunctions(f, ly);
      var trbody = CondApplyBox(f.tok, etranBody.TrExpr(bodyWithSubst), f.Body.Type, f.ResultType);
      tastyVegetarianOption = BplAnd(etranBody.CanCallAssumption(bodyWithSubst),
        BplAnd(TrFunctionSideEffect(bodyWithSubst, etranBody), Bpl.Expr.Eq(funcAppl, trbody)));
    }

    QKeyValue kv = null;
    if (lits != null) {
      kv = new QKeyValue(f.tok, "weight", new List<object>() { Bpl.Expr.Literal(3) }, null);
    }

    Bpl.Expr ax = BplForall(f.tok, new List<Bpl.TypeVariable>(), forallFormals, kv, tr,
      Bpl.Expr.Imp(ante, tastyVegetarianOption));
    var activate = AxiomActivation(f, etran);
    string comment;
    comment = "definition axiom for " + f.FullSanitizedName;
    if (lits != null) {
      if (lits.Count == f.Formals.Count + (f.IsStatic ? 0 : 1)) {
        comment += " for all literals";
      } else {
        comment += " for decreasing-related literals";
      }
    }

    if (RevealedInScope(f)) {
      comment += " (revealed)";
    } else {
      comment += " (opaque)";
    }
    return new Axiom(f.tok, Bpl.Expr.Imp(activate, ax), comment);
  }


  Expr TrFunctionSideEffect(Expression expr, ExpressionTranslator etran) {
    Expr e = Bpl.Expr.True;
    if (expr is StmtExpr) {
      // if there is a call to reveal_ lemma, we need to record its side effect.
      var stmt = ((StmtExpr)expr).S;
      e = TrFunctionSideEffect(stmt, etran);
    }
    return e;
  }

  Expr TrFunctionSideEffect(Statement stmt, ExpressionTranslator etran) {
    Expr e = Bpl.Expr.True;
    e = TrStmtSideEffect(e, stmt, etran);
    foreach (var ss in stmt.SubStatements) {
      e = TrStmtSideEffect(e, ss, etran);
    }
    return e;
  }

  Expr TrStmtSideEffect(Expr e, Statement stmt, ExpressionTranslator etran) {
    if (stmt is CallStmt) {
      var call = (CallStmt)stmt;
      var m = call.Method;
      if (IsOpaqueRevealLemma(m)) {
        List<Expression> args = Attributes.FindExpressions(m.Attributes, "fuel");
        if (args != null) {
          MemberSelectExpr selectExpr = args[0].Resolved as MemberSelectExpr;
          if (selectExpr != null) {
            Function f = selectExpr.Member as Function;
            FuelConstant fuelConstant = this.functionFuel.Find(x => x.f == f);
            if (fuelConstant != null) {
              Bpl.Expr startFuel = fuelConstant.startFuel;
              Bpl.Expr startFuelAssert = fuelConstant.startFuelAssert;
              Bpl.Expr moreFuel_expr = fuelConstant.MoreFuel(sink, predef, f.IdGenerator);
              Bpl.Expr layer = etran.layerInterCluster.LayerN(1, moreFuel_expr);
              Bpl.Expr layerAssert = etran.layerInterCluster.LayerN(2, moreFuel_expr);

              e = BplAnd(e, Bpl.Expr.Eq(startFuel, layer));
              e = BplAnd(e, Bpl.Expr.Eq(startFuelAssert, layerAssert));
              e = BplAnd(e, Bpl.Expr.Eq(this.FunctionCall(f.tok, BuiltinFunction.AsFuelBottom, null, moreFuel_expr), moreFuel_expr));
            }
          }
        }
      }
    } else if (stmt is RevealStmt) {
      var reveal = (RevealStmt)stmt;
      foreach (var s in reveal.ResolvedStatements) {
        e = BplAnd(e, TrFunctionSideEffect(s, etran));
      }
    }
    return e;
  }


  public string FunctionHandle(Function f) {
    Contract.Requires(f != null);
    string name;
    if (functionHandles.TryGetValue(f, out name)) {
      Contract.Assert(name != null);
    } else {
      name = f.FullSanitizedName + "#Handle";
      functionHandles[f] = name;
      var args = new List<Bpl.Expr>();
      var vars = MkTyParamBinders(GetTypeParams(f), out args);
      var argsRequires = new List<Bpl.Expr>(args); // Requires don't have reveal parameters
      var formals = MkTyParamFormals(GetTypeParams(f), false, true);
      var tyargs = new List<Bpl.Expr>();
      foreach (var fm in f.Formals) {
        tyargs.Add(TypeToTy(fm.Type));
      }
      tyargs.Add(TypeToTy(f.ResultType));
      if (f.IsFuelAware()) {
        vars.Add(BplBoundVar("$ly", predef.LayerType, out var ly));
        args.Add(ly);
        argsRequires.Add(ly);
        formals.Add(BplFormalVar("$fuel", predef.LayerType, true));
        AddFuelSuccSynonymAxiom(f, true);
      }
      if (f.IsOpaque || f.IsMadeImplicitlyOpaque(options)) {
        vars.Add(BplBoundVar("$reveal", Boogie.Type.Bool, out var reveal));
        args.Add(reveal);
        formals.Add(BplFormalVar("$reveal", Boogie.Type.Bool, true));
      }

      Func<List<Bpl.Expr>, List<Bpl.Expr>> SnocSelf = x => x;
      Func<List<Bpl.Expr>, List<Bpl.Expr>> SnocPrevH = x => x;
      Expression selfExpr;
      Dictionary<IVariable, Expression> rhs_dict = new Dictionary<IVariable, Expression>();
      if (f is TwoStateFunction) {
        // also add previous-heap to the list of fixed arguments of the handle
        var prevH = BplBoundVar("$prevHeap", predef.HeapType, vars);
        formals.Add(BplFormalVar("h", predef.HeapType, true));
        SnocPrevH = xs => Snoc(xs, prevH);
      }
      if (f.IsStatic) {
        selfExpr = null;
      } else {
        var selfTy = TrType(UserDefinedType.FromTopLevelDecl(f.tok, f.EnclosingClass));
        var self = BplBoundVar("$self", selfTy, vars);
        formals.Add(BplFormalVar("self", selfTy, true));
        SnocSelf = xs => Snoc(xs, self);
        var wrapperType = UserDefinedType.FromTopLevelDecl(f.tok, f.EnclosingClass);
        selfExpr = new BoogieWrapper(self, wrapperType);
      }

      // F#Handle(Ty, .., Ty, LayerType, ref) : HandleType
      sink.AddTopLevelDeclaration(
        new Bpl.Function(f.tok, name, formals, BplFormalVar(null, predef.HandleType, false)));

      var bvars = new List<Bpl.Variable>();
      var lhs_args = new List<Bpl.Expr>();
      var rhs_args = new List<Bpl.Expr>();
      var func_vars = new List<Bpl.Variable>();
      var func_args = new List<Bpl.Expr>();
      var boxed_func_args = new List<Bpl.Expr>();

      var idGen = f.IdGenerator.NestedFreshIdGenerator("$fh$");
      foreach (var fm in f.Formals) {
        string fm_name = idGen.FreshId("x#");
        // Box and its [Unbox]args
        var fe = BplBoundVar(fm_name, predef.BoxType, bvars);
        lhs_args.Add(fe);
        var be = UnboxUnlessInherentlyBoxed(fe, fm.Type);
        rhs_args.Add(be);

        rhs_dict[fm] = new BoogieWrapper(be, fm.Type);
        // args and its [Box]args
        var arg = BplBoundVar(fm_name, TrType(fm.Type), func_vars);
        func_args.Add(arg);
        var boxed = BoxIfNotNormallyBoxed(arg.tok, arg, fm.Type);
        boxed_func_args.Add(boxed);
      }

      var h = BplBoundVar("$heap", predef.HeapType, vars);

      int arity = f.Formals.Count;

      {
        // Apply(Ty.., F#Handle( Ty1, ..., TyN, Layer, self), Heap, arg1, ..., argN)
        //   = [Box] F(Ty1, .., TyN, Layer, Heap, self, [Unbox] arg1, .., [Unbox] argN)

        var fhandle = FunctionCall(f.tok, name, predef.HandleType, SnocSelf(SnocPrevH(args)));
        var lhs = FunctionCall(f.tok, Apply(arity), TrType(f.ResultType),
          Concat(tyargs, Cons(h, Cons(fhandle, lhs_args))));
        var args_h = f.ReadsHeap ? Snoc(SnocPrevH(args), h) : args;
        var rhs = FunctionCall(f.tok, f.FullSanitizedName, TrType(f.ResultType), Concat(SnocSelf(args_h), rhs_args));
        var rhs_boxed = BoxIfNotNormallyBoxed(rhs.tok, rhs, f.ResultType);

        AddOtherDefinition(GetOrCreateFunction(f), (new Axiom(f.tok,
          BplForall(Concat(vars, bvars), BplTrigger(lhs), Bpl.Expr.Eq(lhs, rhs_boxed)))));
      }

      {
        // As a first approximation, the following axiom is of the form:
        // Requires(Ty.., F#Handle( Ty1, ..., TyN, Layer, reveal, self), Heap, arg1, ..., argN)
        //   = F#Requires(Ty1, .., TyN, Layer, Heap, self, [Unbox] arg1, .., [Unbox] argN)
        // However, .reads ands .requires functions require special attention.
        // To understand the rationale for these axioms, refer to the section on arrow types of the reference manual.
        // The requires clause of the .requires function is simply true.
        // The requires clause of the .reads function checks that the precondtion of the receiving function holds.

        var fhandle = FunctionCall(f.tok, name, predef.HandleType, SnocSelf(SnocPrevH(args)));
        var lhs = FunctionCall(f.tok, Requires(arity), Bpl.Type.Bool, Concat(tyargs, Cons(h, Cons(fhandle, lhs_args))));
        Bpl.Expr rhs;
        if (f.EnclosingClass is ArrowTypeDecl && f.Name == "requires") {
          AddOtherDefinition(GetOrCreateFunction(f), new Axiom(f.tok,
              BplForall(Concat(vars, bvars), BplTrigger(lhs), Bpl.Expr.Eq(lhs, Bpl.Expr.True))));
        } else if (f.EnclosingClass is ArrowTypeDecl && f.Name == "reads") {
          var args_h = f.ReadsHeap ? Snoc(SnocPrevH(argsRequires), h) : argsRequires;
          var pre = FunctionCall(f.tok, Requires(arity), Bpl.Type.Bool, Concat(SnocSelf(args_h), lhs_args));
          AddOtherDefinition(GetOrCreateFunction(f), (new Axiom(f.tok,
            BplForall(Concat(vars, bvars), BplTrigger(lhs), Bpl.Expr.Eq(lhs, pre)))));
        } else {
          var args_h = f.ReadsHeap ? Snoc(SnocPrevH(argsRequires), h) : argsRequires;
          rhs = FunctionCall(f.tok, RequiresName(f), Bpl.Type.Bool, Concat(SnocSelf(args_h), rhs_args));
          AddOtherDefinition(GetOrCreateFunction(f), new Axiom(f.tok,
            BplForall(Concat(vars, bvars), BplTrigger(lhs), Bpl.Expr.Eq(lhs, rhs))));
        }


      }

      {
        // As a first approximation, the following axiom is of the form:
        // Reads(Ty.., F#Handle( Ty1, ..., TyN, Layer, self), Heap, arg1, ..., argN)
        //   =  $Frame_F(args...)
        // However, .reads ands .requires functions require special attention.
        // To understand the rationale for these axioms, refer to the section on arrow types of the reference manual.
        // In both cases, the precondition of the receiving function must be checked before its reads clause can
        // be referred to.

        var fhandle = FunctionCall(f.tok, name, predef.HandleType, SnocSelf(SnocPrevH(args)));
        Bpl.Expr lhs_inner = FunctionCall(f.tok, Reads(arity), TrType(program.SystemModuleManager.ObjectSetType()), Concat(tyargs, Cons(h, Cons(fhandle, lhs_args))));

        Bpl.Expr bx; var bxVar = BplBoundVar("$bx", predef.BoxType, out bx);
        Bpl.Expr unboxBx = FunctionCall(f.tok, BuiltinFunction.Unbox, predef.RefType, bx);
        Bpl.Expr lhs = Bpl.Expr.SelectTok(f.tok, lhs_inner, bx);

        var et = new ExpressionTranslator(this, predef, h);
        var rhs = InRWClause_Aux(f.tok, unboxBx, bx, null, f.Reads.Expressions, false, et, selfExpr, rhs_dict);

        if (f.EnclosingClass is ArrowTypeDecl) {
          var args_h = f.ReadsHeap ? Snoc(SnocPrevH(argsRequires), h) : argsRequires;
          var precondition = FunctionCall(f.tok, Requires(arity), Bpl.Type.Bool, Concat(SnocSelf(args_h), lhs_args));
          sink.AddTopLevelDeclaration(new Axiom(f.tok,
            BplForall(Cons(bxVar, Concat(vars, bvars)), BplTrigger(lhs), Bpl.Expr.Imp(precondition, Bpl.Expr.Eq(lhs, rhs)))));
        } else {
          sink.AddTopLevelDeclaration(new Axiom(f.tok,
            BplForall(Cons(bxVar, Concat(vars, bvars)), BplTrigger(lhs), Bpl.Expr.Eq(lhs, rhs))));
        }
      }

      {
        // F(Ty1, .., TyN, Layer, Heap, self, arg1, .., argN)
        // = [Unbox]Apply1(Ty.., F#Handle( Ty1, ..., TyN, Layer, self), Heap, [Box]arg1, ..., [Box]argN)

        var fhandle = FunctionCall(f.tok, name, predef.HandleType, SnocSelf(SnocPrevH(args)));
        var args_h = f.ReadsHeap ? Snoc(SnocPrevH(args), h) : args;
        var lhs = FunctionCall(f.tok, f.FullSanitizedName, TrType(f.ResultType), Concat(SnocSelf(args_h), func_args));
        var rhs = FunctionCall(f.tok, Apply(arity), TrType(f.ResultType), Concat(tyargs, Cons(h, Cons(fhandle, boxed_func_args))));
        var rhs_unboxed = UnboxUnlessInherentlyBoxed(rhs, f.ResultType);
        var tr = BplTriggerHeap(this, f.tok, lhs, f.ReadsHeap ? null : h);

        AddOtherDefinition(GetOrCreateFunction(f), (new Axiom(f.tok,
          BplForall(Concat(vars, func_vars), tr, Bpl.Expr.Eq(lhs, rhs_unboxed)))));
      }
    }
    return name;
  }


  /// <summary>
  /// Generates:
  ///   axiom (forall s, h0: HeapType, h1: HeapType, formals... ::
  ///        { IsHeapAnchor(h0), HeapSucc(h0,h1), F(s,h1,formals) }
  ///        heaps are well-formed and [formals are allocated AND]
  ///        IsHeapAnchor(h0) AND HeapSucc(h0,h1)
  ///        AND
  ///        (forall o: ref, f: Field ::
  ///            o != null [AND h0[o,alloc] AND]  // note that HeapSucc(h0,h1) && h0[o,alloc] ==> h1[o,alloc]
  ///            o in reads clause of formals in h0
  ///            IMPLIES h0[o,f] == h1[o,f])
  ///        IMPLIES
  ///        F(s,h0,formals) == F(s,h1,formals)
  ///      );
  /// Expressions in [...] are omitted if
  ///   - /allocated:0, or
  ///   - /allocated:1, or
  ///   - /allocated:3, except if "reads" clause is "*" of if the function is a two-state function;
  /// see comments in AddArrowTypeAxioms
  /// Also, with /allocated:3, the frame axiom is omitted altogether if the (one-state) function has an
  /// empty "reads" clause (because then the function doesn't take a heap argument at all).
  /// </summary>
  void AddFrameAxiom(Function f) {
    Contract.Requires(f != null);
    Contract.Requires(sink != null && predef != null);

    var comment = "frame axiom for " + f.FullSanitizedName;
    // This is the general case
    Bpl.Expr prevH = null;
    Bpl.BoundVariable prevHVar = null;
    Bpl.Expr reveal = null;
    Bpl.BoundVariable revealVar = null;
    if (f.IsOpaque || f.IsMadeImplicitlyOpaque(options)) {
      revealVar = BplBoundVar("$reveal", Bpl.Type.Bool, out reveal);
    }
    if (f is TwoStateFunction) {
      // The previous-heap argument is the same for both function arguments.  That is,
      // the frame axiom says nothing about functions invoked with different previous heaps.
      prevHVar = BplBoundVar("$prevHeap", predef.HeapType, out prevH);
    }
    Bpl.Expr h0; var h0Var = BplBoundVar("$h0", predef.HeapType, out h0);
    Bpl.Expr h1; var h1Var = BplBoundVar("$h1", predef.HeapType, out h1);

    var etran0 = new ExpressionTranslator(this, predef, h0);
    var etran1 = new ExpressionTranslator(this, predef, h1);

    Bpl.Expr wellFormed = Bpl.Expr.And(
      FunctionCall(f.tok, BuiltinFunction.IsGoodHeap, null, etran0.HeapExpr),
      FunctionCall(f.tok, BuiltinFunction.IsGoodHeap, null, etran1.HeapExpr));

    Bpl.Expr o; var oVar = BplBoundVar("$o", predef.RefType, out o);
    Bpl.Expr field; var fieldVar = BplBoundVar("$f", predef.FieldName(f.tok), out field);
    Bpl.Expr oNotNull = Bpl.Expr.Neq(o, predef.Null);
    Bpl.Expr oNotNullAlloced = oNotNull;
    Bpl.Expr unchanged = Bpl.Expr.Eq(ReadHeap(f.tok, h0, o, field), ReadHeap(f.tok, h1, o, field));

    Bpl.Expr h0IsHeapAnchor = FunctionCall(h0.tok, BuiltinFunction.IsHeapAnchor, null, h0);
    Bpl.Expr heapSucc = HeapSucc(h0, h1);
    Bpl.Expr r0 = InRWClause(f.tok, o, field, f.Reads.Expressions, etran0, null, null);
    Bpl.Expr q0 = new Bpl.ForallExpr(f.tok, new List<TypeVariable> { }, new List<Variable> { oVar, fieldVar },
      Bpl.Expr.Imp(Bpl.Expr.And(oNotNullAlloced, r0), unchanged));

    List<Bpl.Expr> tyexprs;
    var bvars = MkTyParamBinders(GetTypeParams(f), out tyexprs);
    var f0args = new List<Bpl.Expr>(tyexprs);
    var f1args = new List<Bpl.Expr>(tyexprs);
    var f0argsCanCall = new List<Bpl.Expr>(tyexprs);
    var f1argsCanCall = new List<Bpl.Expr>(tyexprs);
    if (f.IsFuelAware()) {
      Bpl.Expr s; var sV = BplBoundVar("$ly", predef.LayerType, out s);
      bvars.Add(sV);
      f0args.Add(s); f1args.Add(s);  // but don't add to f0argsCanCall or f1argsCanCall
    }

    if (reveal != null) {
      bvars.Add(revealVar);
      f0args.Add(reveal); f1args.Add(reveal);
    }

    if (prevH != null) {
      bvars.Add(prevHVar);
      f0args.Add(prevH); f1args.Add(prevH); f0argsCanCall.Add(prevH); f1argsCanCall.Add(prevH);
    }
    bvars.Add(h0Var); bvars.Add(h1Var);
    f0args.Add(h0); f1args.Add(h1); f0argsCanCall.Add(h0); f1argsCanCall.Add(h1);

    var useAlloc = f.Reads.Expressions.Exists(fe => fe.E is WildcardExpr) ? ISALLOC : NOALLOC;
    if (!f.IsStatic) {
      Bpl.Expr th; var thVar = BplBoundVar("this", TrReceiverType(f), out th);
      bvars.Add(thVar);
      f0args.Add(th); f1args.Add(th); f0argsCanCall.Add(th); f1argsCanCall.Add(th);

      Type thisType = ModuleResolver.GetReceiverType(f.tok, f);
      Bpl.Expr wh = Bpl.Expr.And(ReceiverNotNull(th), GetWhereClause(f.tok, th, thisType, etran0, useAlloc));
      wellFormed = Bpl.Expr.And(wellFormed, wh);
    }

    // (formalsAreWellFormed[h0] || canCallF(h0,...)) && (formalsAreWellFormed[h1] || canCallF(h1,...))
    Bpl.Expr fwf0 = Bpl.Expr.True;
    Bpl.Expr fwf1 = Bpl.Expr.True;
    foreach (Formal p in f.Formals) {
      Bpl.BoundVariable bv = new Bpl.BoundVariable(p.tok, new Bpl.TypedIdent(p.tok, p.AssignUniqueName(f.IdGenerator), TrType(p.Type)));
      bvars.Add(bv);
      Bpl.Expr formal = new Bpl.IdentifierExpr(p.tok, bv);
      f0args.Add(formal); f1args.Add(formal); f0argsCanCall.Add(formal); f1argsCanCall.Add(formal);
      Bpl.Expr wh = GetWhereClause(p.tok, formal, p.Type, etran0, useAlloc);
      if (wh != null) { fwf0 = Bpl.Expr.And(fwf0, wh); }
    }
    var canCall = new Bpl.FunctionCall(new Bpl.IdentifierExpr(f.tok, f.FullSanitizedName + "#canCall", Bpl.Type.Bool));
    wellFormed = Bpl.Expr.And(wellFormed, Bpl.Expr.And(
      Bpl.Expr.Or(new Bpl.NAryExpr(f.tok, canCall, f0argsCanCall), fwf0),
      Bpl.Expr.Or(new Bpl.NAryExpr(f.tok, canCall, f1argsCanCall), fwf1)));

    /*
    DR: I conjecture that this should be enough,
        as the requires is preserved when the frame is:

    wellFormed = Bpl.Expr.And(wellFormed,
      Bpl.Expr.Or(new Bpl.NAryExpr(f.tok, canCall, f0argsCanCall), fwf0));
    */

    var fn = new Bpl.FunctionCall(new Bpl.IdentifierExpr(f.tok, f.FullSanitizedName, TrType(f.ResultType)));
    var F0 = new Bpl.NAryExpr(f.tok, fn, f0args);
    var F1 = new Bpl.NAryExpr(f.tok, fn, f1args);
    var eq = Bpl.Expr.Eq(F0, F1);
    var tr = new Bpl.Trigger(f.tok, true, new List<Bpl.Expr> { h0IsHeapAnchor, heapSucc, F1 });

    var ax = new Bpl.ForallExpr(f.tok, new List<Bpl.TypeVariable>(), bvars, null, tr,
      Bpl.Expr.Imp(Bpl.Expr.And(wellFormed, Bpl.Expr.And(h0IsHeapAnchor, heapSucc)),
      Bpl.Expr.Imp(q0, eq)));
    sink.AddTopLevelDeclaration(new Bpl.Axiom(f.tok, ax, comment));
  }
}