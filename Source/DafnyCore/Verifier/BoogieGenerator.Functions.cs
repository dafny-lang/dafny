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
        var surrogate = new ThisSurrogate(f.Tok, ModuleResolver.GetReceiverType(f.Tok, f));
        allFormals.Add(surrogate);
        if (usesThis != null) {
          decs.Add(surrogate);
        }
      }
      foreach (var formal in f.Ins) {
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
    Contract.Requires(Predef != null);
    Contract.Requires(f.EnclosingClass != null);

    bool readsHeap = f.ReadsHeap;
    foreach (AttributedExpression e in f.Req.Concat(ens)) {
      readsHeap = readsHeap || UsesHeap(e.E);
    }

    ExpressionTranslator etranHeap;
    ExpressionTranslator etran;
    Bpl.BoundVariable bvPrevHeap = null;
    if (f is TwoStateFunction) {
      bvPrevHeap = new Bpl.BoundVariable(f.Tok, new Bpl.TypedIdent(f.Tok, "$prevHeap", Predef.HeapType));
      etran = new ExpressionTranslator(this, Predef,
        f.ReadsHeap ? new Bpl.IdentifierExpr(f.Tok, Predef.HeapVarName, Predef.HeapType) : null,
        new Bpl.IdentifierExpr(f.Tok, bvPrevHeap), f);
      etranHeap = etran;
    } else {
      etranHeap = new ExpressionTranslator(this, Predef, f.Tok, f);
      etran = readsHeap ? etranHeap : new ExpressionTranslator(this, Predef, (Bpl.Expr)null, f);
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
      layer = new Bpl.BoundVariable(f.Tok, new Bpl.TypedIdent(f.Tok, "$ly", Predef.LayerType));
      formals.Add(layer);
      etran = etran.WithCustomFuelSetting(new CustomFuelSettings { { f, new FuelSetting(this, 0, new Bpl.IdentifierExpr(f.Tok, layer)) } });
      //etran = etran.WithLayer(new Bpl.IdentifierExpr(f.Tok, layer));
      // Note, "layer" is not added to "args" here; rather, that's done below, as needed
    } else {
      layer = null;
    }

    Bpl.BoundVariable reveal;
    if (f.IsOpaque || f.IsMadeImplicitlyOpaque(options)) {
      reveal = new Bpl.BoundVariable(f.Tok, new Bpl.TypedIdent(f.Tok, "$reveal", Boogie.Type.Bool));
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
      var goodHeap = FunctionCall(f.Tok, BuiltinFunction.IsGoodHeap, null, etran.Old.HeapExpr);
      ante = BplAnd(ante, goodHeap);
      anteIsAlloc = BplAnd(anteIsAlloc, goodHeap);
    }
    var bvHeap = new Bpl.BoundVariable(f.Tok, new Bpl.TypedIdent(f.Tok, Predef.HeapVarName, Predef.HeapType));
    if (f.ReadsHeap) {
      args.Add(new Bpl.IdentifierExpr(f.Tok, bvHeap));
    }
    // ante:  $IsGoodHeap($Heap) && $HeapSucc($prevHeap, $Heap) && this != null && formals-have-the-expected-types &&
    if (readsHeap) {
      Bpl.Expr goodHeap = FunctionCall(f.Tok, BuiltinFunction.IsGoodHeap, null, etranHeap.HeapExpr);
      formals.Add(bvHeap);
      ante = BplAnd(ante, goodHeap);
      anteIsAlloc = BplAnd(anteIsAlloc, f.ReadsHeap ? goodHeap : Bpl.Expr.True);
      if (f is TwoStateFunction) {
        var heapSucc = HeapSucc(etran.Old.HeapExpr, etran.HeapExpr);
        ante = BplAnd(ante, heapSucc);
        anteIsAlloc = BplAnd(anteIsAlloc, f.ReadsHeap ? heapSucc : Bpl.Expr.True);
      }
    }
    // ante:  conditions on bounded type parameters
    foreach (var typeBoundAxiom in TypeBoundAxioms(f.Tok, Concat(f.EnclosingClass.TypeArgs, f.TypeArgs))) {
      ante = BplAnd(ante, typeBoundAxiom);
      anteIsAlloc = BplAnd(anteIsAlloc, typeBoundAxiom);
    }

    if (!f.IsStatic) {
      var bvThis = new Bpl.BoundVariable(f.Tok, new Bpl.TypedIdent(f.Tok, etran.This, TrReceiverType(f)));
      formals.Add(bvThis);
      olderInParams.Add(bvThis);
      var bvThisIdExpr = new Bpl.IdentifierExpr(f.Tok, bvThis);
      args.Add(bvThisIdExpr);
      // add well-typedness conjunct to antecedent
      Type thisType = ModuleResolver.GetReceiverType(f.Tok, f);
      Bpl.Expr wh = BplAnd(
        ReceiverNotNull(bvThisIdExpr),
        (f is TwoStateFunction ? etran.Old : etran).GoodRef(f.Tok, bvThisIdExpr, thisType));
      ante = BplAnd(ante, wh);
      anteIsAlloc = BplAnd(anteIsAlloc, ReceiverNotNull(bvThisIdExpr));
      wh = GetWhereClause(f.Tok, bvThisIdExpr, thisType, f is TwoStateFunction ? etranHeap.Old : etranHeap, ISALLOC, true);
      if (wh != null) {
        anteIsAlloc = BplAnd(anteIsAlloc, wh);
      }
    }
    foreach (Formal p in f.Ins) {
      var bv = new Bpl.BoundVariable(p.Tok, new Bpl.TypedIdent(p.Tok, p.AssignUniqueName(CurrentDeclaration.IdGenerator), TrType(p.Type)));
      Bpl.Expr formal = new Bpl.IdentifierExpr(p.Tok, bv);
      formals.Add(bv);
      olderInParams.Add(bv);
      args.Add(formal);
      // add well-typedness conjunct to antecedent
      Bpl.Expr wh = GetWhereClause(p.Tok, formal, p.Type, p.IsOld ? etran.Old : etran, ISALLOC);
      if (wh != null) { ante = BplAnd(ante, wh); }
      wh = GetWhereClause(p.Tok, formal, p.Type, p.IsOld ? etranHeap.Old : etranHeap, ISALLOC);
      if (wh != null) { anteIsAlloc = BplAnd(anteIsAlloc, wh); }
    }

    Bpl.Expr funcAppl;
    {
      var funcID = new Bpl.IdentifierExpr(f.Tok, f.FullSanitizedName, TrType(f.ResultType));
      var funcArgs = new List<Bpl.Expr>();
      funcArgs.AddRange(tyargs);
      /*
      if (f.IsFueled) {
          funcArgs.Add(etran.layerInterCluster.GetFunctionFuel(f));
      } else if (layer != null) {
         var ly = new Bpl.IdentifierExpr(f.Tok, layer);
         funcArgs.Add(FunctionCall(f.Tok, BuiltinFunction.LayerSucc, null, ly));
      }
       */
      if (layer != null) {
        funcArgs.Add(new Bpl.IdentifierExpr(f.Tok, layer));
      }

      if (reveal != null) {
        funcArgs.Add(new Bpl.IdentifierExpr(f.Tok, reveal));
      }

      funcArgs.AddRange(args);
      funcAppl = new Bpl.NAryExpr(f.Tok, new Bpl.FunctionCall(funcID), funcArgs);
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
    Bpl.IdentifierExpr canCallFuncID = new Bpl.IdentifierExpr(f.Tok, f.FullSanitizedName + "#canCall", Bpl.Type.Bool);
    Bpl.Expr useViaCanCall = new Bpl.NAryExpr(f.Tok, new Bpl.FunctionCall(canCallFuncID), Concat(tyargs, args));

    // ante := useViaCanCall || (useViaContext && typeAnte && pre)
    ante = BplOr(useViaCanCall, BplAnd(useViaContext, BplAnd(ante, pre)));
    anteIsAlloc = BplOr(useViaCanCall, BplAnd(useViaContext, BplAnd(anteIsAlloc, pre)));

    Bpl.Trigger tr = BplTriggerHeap(this, f.Tok, funcAppl,
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
    Bpl.Expr whr = GetWhereClause(f.Tok, funcAppl, f.ResultType, etran, NOALLOC);
    if (whr != null) { post = BplAnd(post, whr); }

    Bpl.Expr axBody = BplImp(ante, post);
    Bpl.Expr ax = BplForall(f.Tok, new List<Bpl.TypeVariable>(), formals, null, tr, axBody);
    var activate = AxiomActivation(f, etran);
    string comment = "consequence axiom for " + f.FullSanitizedName;
    if (RemoveLit(axBody) != Bpl.Expr.True) {
      var consequenceExpr = BplImp(activate, ax);
      var consequenceAxiom = new Bpl.Axiom(f.Tok, consequenceExpr, comment);
      AddOtherDefinition(boogieFunction, consequenceAxiom);
    }

    if (f.ResultType.MayInvolveReferences) {
      whr = GetWhereClause(f.Tok, funcAppl, f.ResultType, etranHeap, ISALLOC, true);
      if (whr != null) {
        if (readsHeap) {
          Contract.Assert(formals.Contains(bvHeap));
        } else {
          formals = Util.Cons(bvHeap, formals);
          var goodHeap = FunctionCall(f.Tok, BuiltinFunction.IsGoodHeap, null, etranHeap.HeapExpr);
          anteIsAlloc = BplAnd(anteIsAlloc, goodHeap);
        }

        axBody = BplImp(anteIsAlloc, whr);
        ax = BplForall(f.Tok, new List<Bpl.TypeVariable>(), formals, null, BplTrigger(whr), axBody);

        if (RemoveLit(axBody) != Bpl.Expr.True) {
          comment = "alloc consequence axiom for " + f.FullSanitizedName;
          var allocConsequenceAxiom = new Bpl.Axiom(f.Tok, BplImp(activate, ax), comment);
          AddOtherDefinition(boogieFunction, allocConsequenceAxiom);
        }
      }
    }
  }

  /// <summary>
  /// The list of formals "lits" is allowed to contain an object of type ThisSurrogate, which indicates that
  /// the receiver parameter of the function should be included among the lit formals.
  /// </summary>
  private Axiom GetFunctionAxiom(Function f, Expression body, List<Formal> lits) {
    Contract.Requires(f != null);
    Contract.Requires(Predef != null);
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
      bvPrevHeap = new Bpl.BoundVariable(f.Tok, new Bpl.TypedIdent(f.Tok, "$prevHeap", Predef.HeapType));
      etran = new ExpressionTranslator(this, Predef,
        f.ReadsHeap ? new Bpl.IdentifierExpr(f.Tok, Predef.HeapVarName, Predef.HeapType) : null,
        new Bpl.IdentifierExpr(f.Tok, bvPrevHeap), f);
    } else {
      etran = readsHeap
        ? new ExpressionTranslator(this, Predef, f.Tok, f)
        : new ExpressionTranslator(this, Predef, (Bpl.Expr)null, f);
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
      layer = new Bpl.BoundVariable(f.Tok, new Bpl.TypedIdent(f.Tok, "$ly", Predef.LayerType));
      forallFormals.Add(layer);
      funcFormals.Add(layer);
      reqFuncArguments.Add(new Bpl.IdentifierExpr(f.Tok, layer));
      // Note, "layer" is not added to "args" here; rather, that's done below, as needed
    } else {
      layer = null;
    }

    if (f.IsOpaque || f.IsMadeImplicitlyOpaque(options)) {
      reveal = new Bpl.BoundVariable(f.Tok, new Bpl.TypedIdent(f.Tok, "$reveal", Boogie.Type.Bool));
      //funcFormals.Add(reveal);
      //reqFuncArguments.Add(new Bpl.IdentifierExpr(f.Tok, reveal));
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
      reqFuncArguments.Add(new Bpl.IdentifierExpr(f.Tok, bvPrevHeap));
      // ante:  $IsGoodHeap($prevHeap) &&
      ante = BplAnd(ante, FunctionCall(f.Tok, BuiltinFunction.IsGoodHeap, null, etran.Old.HeapExpr));
    }

    Bpl.Expr goodHeap = null;
    var bv = new Bpl.BoundVariable(f.Tok, new Bpl.TypedIdent(f.Tok, Predef.HeapVarName, Predef.HeapType));
    if (f.ReadsHeap) {
      funcFormals.Add(bv);
    }

    if (f.ReadsHeap) {
      args.Add(new Bpl.IdentifierExpr(f.Tok, bv));
      reqFuncArguments.Add(new Bpl.IdentifierExpr(f.Tok, bv));
    }

    // ante:  $IsGoodHeap($Heap) && $HeapSucc($prevHeap, $Heap) && this != null && formals-have-the-expected-types &&
    if (readsHeap) {
      forallFormals.Add(bv);
      goodHeap = FunctionCall(f.Tok, BuiltinFunction.IsGoodHeap, null, etran.HeapExpr);
      ante = BplAnd(ante, goodHeap);
    }

    if (f is TwoStateFunction && f.ReadsHeap) {
      ante = BplAnd(ante, HeapSucc(etran.Old.HeapExpr, etran.HeapExpr));
    }

    // ante:  conditions on bounded type parameters
    foreach (var typeBoundAxiom in TypeBoundAxioms(f.Tok, Concat(f.EnclosingClass.TypeArgs, f.TypeArgs))) {
      ante = BplAnd(ante, typeBoundAxiom);
    }

    Expression receiverReplacement = null;
    if (!f.IsStatic) {
      var bvThis = new Bpl.BoundVariable(f.Tok, new Bpl.TypedIdent(f.Tok, etran.This, TrReceiverType(f)));
      forallFormals.Add(bvThis);
      funcFormals.Add(bvThis);
      reqFuncArguments.Add(new Bpl.IdentifierExpr(f.Tok, bvThis));
      var bvThisIdExpr = new Bpl.IdentifierExpr(f.Tok, bvThis);
      if (lits != null && lits.Exists(p => p is ThisSurrogate)) {
        args.Add(Lit(bvThisIdExpr));
        var th = new ThisExpr(f);
        var l = new UnaryOpExpr(f.Tok, UnaryOpExpr.Opcode.Lit, th) {
          Type = th.Type
        };
        receiverReplacement = l;
      } else {
        args.Add(bvThisIdExpr);
      }

      // add well-typedness conjunct to antecedent
      Type thisType = ModuleResolver.GetReceiverType(f.Tok, f);
      Bpl.Expr wh = BplAnd(
        ReceiverNotNull(bvThisIdExpr),
        (f is TwoStateFunction ? etran.Old : etran).GoodRef(f.Tok, bvThisIdExpr, thisType));
      ante = BplAnd(ante, wh);
    }

    var typeMap = new Dictionary<TypeParameter, Type>();
    var anteReqAxiom = ante; // note that antecedent so far is the same for #requires axioms, even the receiver parameter of a two-state function
    var substMap = new Dictionary<IVariable, Expression>();
    foreach (Formal p in f.Ins) {
      var pType = p.Type.Subst(typeMap);
      bv = new Bpl.BoundVariable(p.Tok,
        new Bpl.TypedIdent(p.Tok, p.AssignUniqueName(CurrentDeclaration.IdGenerator), TrType(pType)));
      forallFormals.Add(bv);
      funcFormals.Add(bv);
      reqFuncArguments.Add(new Bpl.IdentifierExpr(f.Tok, bv));
      Bpl.Expr formal = new Bpl.IdentifierExpr(p.Tok, bv);
      if (lits != null && lits.Contains(p) && !substMap.ContainsKey(p)) {
        args.Add(Lit(formal));
        var ie = new IdentifierExpr(p.Tok, p.AssignUniqueName(f.IdGenerator));
        ie.Var = p;
        ie.Type = ie.Var.Type;
        var l = new UnaryOpExpr(p.Tok, UnaryOpExpr.Opcode.Lit, ie);
        l.Type = ie.Var.Type;
        substMap.Add(p, l);
      } else {
        args.Add(formal);
      }

      // add well-typedness conjunct to antecedent
      Bpl.Expr wh = GetWhereClause(p.Tok, formal, pType, p.IsOld ? etran.Old : etran, NOALLOC);
      if (wh != null) {
        ante = BplAnd(ante, wh);
      }

      wh = GetWhereClause(p.Tok, formal, pType, etran, NOALLOC);
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
      foreach (var formal in f.Ins) {
        if (formal.IsOld) {
          var dafnyFormalIdExpr = new IdentifierExpr(formal.Tok, formal);
          preRA = BplAnd(preRA, MkIsAlloc(etran.TrExpr(dafnyFormalIdExpr), formal.Type, etran.Old.HeapExpr));
        }

        index++;
      }

      preReqAxiom = BplAnd(preRA, pre);
    }

    // Add the precondition function and its axiom (which is equivalent to the anteReqAxiom)
    if (body == null || (RevealedInScope(f) && lits == null)) {
      var precondF = new Bpl.Function(f.Tok,
        RequiresName(f), new List<Bpl.TypeVariable>(),
        funcFormals.ConvertAll(v => (Bpl.Variable)BplFormalVar(null, v.TypedIdent.Type, true)),
        BplFormalVar(null, Bpl.Type.Bool, false));
      sink.AddTopLevelDeclaration(precondF);

      var appl = FunctionCall(f.Tok, RequiresName(f), Bpl.Type.Bool, reqFuncArguments);
      Bpl.Trigger trig = BplTriggerHeap(this, f.Tok, appl, readsHeap ? etran.HeapExpr : null);
      // axiom (forall params :: { f#requires(params) }  ante ==> f#requires(params) == pre);
      AddOtherDefinition(precondF, new Axiom(f.Tok,
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
    Bpl.IdentifierExpr canCallFuncID = new Bpl.IdentifierExpr(f.Tok, f.FullSanitizedName + "#canCall", Bpl.Type.Bool);
    Bpl.Expr useViaCanCall = new Bpl.NAryExpr(f.Tok, new Bpl.FunctionCall(canCallFuncID), Concat(tyargs, args));

    // ante := useViaCanCall || (useViaContext && typeAnte && pre)
    ante = BplOr(useViaCanCall, ante);

    Bpl.Expr funcAppl;
    {
      var funcID = new Bpl.IdentifierExpr(f.Tok, f.FullSanitizedName, TrType(f.ResultType));
      var funcArgs = new List<Bpl.Expr>();
      funcArgs.AddRange(tyargs);
      if (layer != null) {
        var ly = new Bpl.IdentifierExpr(f.Tok, layer);
        //if (lits == null) {
        funcArgs.Add(LayerSucc(ly));
        //} else {
        //  funcArgs.Add(ly);
        //}
      }

      if (reveal != null) {
        funcArgs.Add(new Bpl.LiteralExpr(f.Tok, true));
      }

      funcArgs.AddRange(args);
      funcAppl = new Bpl.NAryExpr(f.Tok, new Bpl.FunctionCall(funcID), funcArgs);
    }

    Bpl.Trigger tr = BplTriggerHeap(this, f.Tok, funcAppl, readsHeap ? etran.HeapExpr : null);
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
        ly = new Bpl.IdentifierExpr(f.Tok, layer);
        if (lits != null) {
          // Lit axiom doesn't consume any fuel
          ly = LayerSucc(ly);
        }
      }

      var etranBody = layer == null ? etran : etran.LimitedFunctions(f, ly);
      var trbody = AdaptBoxing(f.Tok, etranBody.TrExpr(bodyWithSubst), f.Body.Type, f.ResultType);
      tastyVegetarianOption = BplAnd(etranBody.CanCallAssumption(bodyWithSubst),
        BplAnd(TrFunctionSideEffect(bodyWithSubst, etranBody), Bpl.Expr.Eq(funcAppl, trbody)));
    }

    QKeyValue kv = null;
    if (lits != null) {
      kv = new QKeyValue(f.Tok, "weight", new List<object>() { Bpl.Expr.Literal(3) }, null);
    }

    Bpl.Expr ax = BplForall(f.Tok, new List<Bpl.TypeVariable>(), forallFormals, kv, tr,
      BplImp(ante, tastyVegetarianOption));
    var activate = AxiomActivation(f, etran);
    string comment;
    comment = "definition axiom for " + f.FullSanitizedName;
    if (lits != null) {
      if (lits.Count == f.Ins.Count + (f.IsStatic ? 0 : 1)) {
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
    var axe = new Axiom(f.Tok, BplImp(activate, ax), comment) {
      CanHide = true
    };
    if (proofDependencies == null) {
      return axe;
    }

    proofDependencies.SetCurrentDefinition(f.FullSanitizedName, f);
    proofDependencies.AddProofDependencyId(axe, f.Tok, new FunctionDefinitionDependency(f));
    return axe;
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
      foreach (var fm in f.Ins) {
        tyargs.Add(TypeToTy(fm.Type));
      }
      tyargs.Add(TypeToTy(f.ResultType));
      if (f.IsFuelAware()) {
        vars.Add(BplBoundVar("$ly", Predef.LayerType, out var ly));
        args.Add(ly);
        argsRequires.Add(ly);
        formals.Add(BplFormalVar("$fuel", Predef.LayerType, true));
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
        var prevH = BplBoundVar("$prevHeap", Predef.HeapType, vars);
        formals.Add(BplFormalVar("h", Predef.HeapType, true));
        SnocPrevH = xs => Snoc(xs, prevH);
      }
      if (f.IsStatic) {
        selfExpr = null;
      } else {
        var selfTy = TrType(UserDefinedType.FromTopLevelDecl(f.Tok, f.EnclosingClass));
        var self = BplBoundVar("$self", selfTy, vars);
        formals.Add(BplFormalVar("self", selfTy, true));
        SnocSelf = xs => Snoc(xs, self);
        var wrapperType = UserDefinedType.FromTopLevelDecl(f.Tok, f.EnclosingClass);
        selfExpr = new BoogieWrapper(self, wrapperType);
      }

      // F#Handle(Ty, .., Ty, LayerType, ref) : HandleType
      sink.AddTopLevelDeclaration(
        new Bpl.Function(f.Tok, name, formals, BplFormalVar(null, Predef.HandleType, false)));

      var bvars = new List<Bpl.Variable>();
      var lhs_args = new List<Bpl.Expr>();
      var rhs_args = new List<Bpl.Expr>();
      var func_vars = new List<Bpl.Variable>();
      var func_args = new List<Bpl.Expr>();
      var boxed_func_args = new List<Bpl.Expr>();

      var idGen = f.IdGenerator.NestedFreshIdGenerator("$fh$");
      foreach (var fm in f.Ins) {
        string fm_name = idGen.FreshId("x#");
        // Box and its [Unbox]args
        var fe = BplBoundVar(fm_name, Predef.BoxType, bvars);
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

      var h = BplBoundVar("$heap", Predef.HeapType, vars);

      int arity = f.Ins.Count;

      {
        // Apply(Ty.., F#Handle( Ty1, ..., TyN, Layer, self), Heap, arg1, ..., argN)
        //   = [Box] F(Ty1, .., TyN, Layer, Heap, self, [Unbox] arg1, .., [Unbox] argN)

        var fhandle = FunctionCall(f.Tok, name, Predef.HandleType, SnocSelf(SnocPrevH(args)));
        var lhs = FunctionCall(f.Tok, Apply(arity), TrType(f.ResultType),
          Concat(tyargs, Cons(h, Cons(fhandle, lhs_args))));
        var args_h = f.ReadsHeap ? Snoc(SnocPrevH(args), h) : args;
        var rhs = FunctionCall(f.Tok, f.FullSanitizedName, TrType(f.ResultType), Concat(SnocSelf(args_h), rhs_args));
        var rhs_boxed = BoxIfNotNormallyBoxed(rhs.tok, rhs, f.ResultType);

        AddOtherDefinition(GetOrCreateFunction(f), (new Axiom(f.Tok,
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

        var fhandle = FunctionCall(f.Tok, name, Predef.HandleType, SnocSelf(SnocPrevH(args)));
        var lhs = FunctionCall(f.Tok, Requires(arity), Bpl.Type.Bool, Concat(tyargs, Cons(h, Cons(fhandle, lhs_args))));
        Bpl.Expr rhs;
        if (f.EnclosingClass is ArrowTypeDecl && f.Name == "requires") {
          AddOtherDefinition(GetOrCreateFunction(f), new Axiom(f.Tok,
              BplForall(Concat(vars, bvars), BplTrigger(lhs), Bpl.Expr.Eq(lhs, Bpl.Expr.True))));
        } else if (f.EnclosingClass is ArrowTypeDecl && f.Name == "reads") {
          var args_h = f.ReadsHeap ? Snoc(SnocPrevH(argsRequires), h) : argsRequires;
          var pre = FunctionCall(f.Tok, Requires(arity), Bpl.Type.Bool, Concat(SnocSelf(args_h), lhs_args));
          AddOtherDefinition(GetOrCreateFunction(f), (new Axiom(f.Tok,
            BplForall(Concat(vars, bvars), BplTrigger(lhs), Bpl.Expr.Eq(lhs, pre)))));
        } else {
          var args_h = f.ReadsHeap ? Snoc(SnocPrevH(argsRequires), h) : argsRequires;
          rhs = FunctionCall(f.Tok, RequiresName(f), Bpl.Type.Bool, Concat(SnocSelf(args_h), rhs_args));
          AddOtherDefinition(GetOrCreateFunction(f), new Axiom(f.Tok,
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

        var fhandle = FunctionCall(f.Tok, name, Predef.HandleType, SnocSelf(SnocPrevH(args)));
        Bpl.Expr lhs_inner = FunctionCall(f.Tok, Reads(arity), TrType(program.SystemModuleManager.ObjectSetType()), Concat(tyargs, Cons(h, Cons(fhandle, lhs_args))));

        Bpl.Expr bx; var bxVar = BplBoundVar("$bx", Predef.BoxType, out bx);
        Bpl.Expr unboxBx = FunctionCall(f.Tok, BuiltinFunction.Unbox, Predef.RefType, bx);
        Bpl.Expr lhs = IsSetMember(f.Tok, lhs_inner, bx, true);

        var et = new ExpressionTranslator(this, Predef, h, f);
        var rhs = InRWClause_Aux(f.Tok, unboxBx, bx, null, f.Reads.Expressions, false, et, selfExpr, rhs_dict);

        if (f.EnclosingClass is ArrowTypeDecl) {
          var args_h = f.ReadsHeap ? Snoc(SnocPrevH(argsRequires), h) : argsRequires;
          var precondition = FunctionCall(f.Tok, Requires(arity), Bpl.Type.Bool, Concat(SnocSelf(args_h), lhs_args));
          sink.AddTopLevelDeclaration(new Axiom(f.Tok,
            BplForall(Cons(bxVar, Concat(vars, bvars)), BplTrigger(lhs), BplImp(precondition, Bpl.Expr.Eq(lhs, rhs)))));
        } else {
          sink.AddTopLevelDeclaration(new Axiom(f.Tok,
            BplForall(Cons(bxVar, Concat(vars, bvars)), BplTrigger(lhs), Bpl.Expr.Eq(lhs, rhs))));
        }
      }

      {
        // F(Ty1, .., TyN, Layer, Heap, self, arg1, .., argN)
        // = [Unbox]Apply1(Ty.., F#Handle( Ty1, ..., TyN, Layer, self), Heap, [Box]arg1, ..., [Box]argN)

        var fhandle = FunctionCall(f.Tok, name, Predef.HandleType, SnocSelf(SnocPrevH(args)));
        var args_h = f.ReadsHeap ? Snoc(SnocPrevH(args), h) : args;
        var lhs = FunctionCall(f.Tok, f.FullSanitizedName, TrType(f.ResultType), Concat(SnocSelf(args_h), func_args));
        var rhs = FunctionCall(f.Tok, Apply(arity), TrType(f.ResultType), Concat(tyargs, Cons(h, Cons(fhandle, boxed_func_args))));
        var rhs_unboxed = UnboxUnlessInherentlyBoxed(rhs, f.ResultType);
        var tr = BplTriggerHeap(this, f.Tok, lhs, f.ReadsHeap ? null : h);

        AddOtherDefinition(GetOrCreateFunction(f), (new Axiom(f.Tok,
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
    Contract.Requires(sink != null && Predef != null);

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
      prevHVar = BplBoundVar("$prevHeap", Predef.HeapType, out prevH);
    }
    Bpl.Expr h0; var h0Var = BplBoundVar("$h0", Predef.HeapType, out h0);
    Bpl.Expr h1; var h1Var = BplBoundVar("$h1", Predef.HeapType, out h1);

    var etran0 = new ExpressionTranslator(this, Predef, h0, f);
    var etran1 = new ExpressionTranslator(this, Predef, h1, f);

    Bpl.Expr wellFormed = BplAnd(
      FunctionCall(f.Tok, BuiltinFunction.IsGoodHeap, null, etran0.HeapExpr),
      FunctionCall(f.Tok, BuiltinFunction.IsGoodHeap, null, etran1.HeapExpr));

    Bpl.Expr o; var oVar = BplBoundVar("$o", Predef.RefType, out o);
    Bpl.Expr field; var fieldVar = BplBoundVar("$f", Predef.FieldName(f.Tok), out field);
    Bpl.Expr oNotNull = Bpl.Expr.Neq(o, Predef.Null);
    Bpl.Expr oNotNullAlloced = oNotNull;
    Bpl.Expr unchanged = Bpl.Expr.Eq(ReadHeap(f.Tok, h0, o, field), ReadHeap(f.Tok, h1, o, field));

    Bpl.Expr h0IsHeapAnchor = FunctionCall(h0.tok, BuiltinFunction.IsHeapAnchor, null, h0);
    Bpl.Expr heapSucc = HeapSucc(h0, h1);
    Bpl.Expr r0 = InRWClause(f.Tok, o, field, f.Reads.Expressions, etran0, null, null);
    Bpl.Expr q0 = new Bpl.ForallExpr(f.Tok, new List<TypeVariable> { }, new List<Variable> { oVar, fieldVar },
      BplImp(BplAnd(oNotNullAlloced, r0), unchanged));

    List<Bpl.Expr> tyexprs;
    var bvars = MkTyParamBinders(GetTypeParams(f), out tyexprs);
    var f0args = new List<Bpl.Expr>(tyexprs);
    var f1args = new List<Bpl.Expr>(tyexprs);
    var f0argsCanCall = new List<Bpl.Expr>(tyexprs);
    var f1argsCanCall = new List<Bpl.Expr>(tyexprs);
    if (f.IsFuelAware()) {
      Bpl.Expr s; var sV = BplBoundVar("$ly", Predef.LayerType, out s);
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

      Type thisType = ModuleResolver.GetReceiverType(f.Tok, f);
      Bpl.Expr wh = BplAnd(ReceiverNotNull(th), GetWhereClause(f.Tok, th, thisType, etran0, useAlloc));
      wellFormed = BplAnd(wellFormed, wh);
    }

    // (formalsAreWellFormed[h0] || canCallF(h0,...)) && (formalsAreWellFormed[h1] || canCallF(h1,...))
    Bpl.Expr fwf0 = Bpl.Expr.True;
    Bpl.Expr fwf1 = Bpl.Expr.True;
    foreach (Formal p in f.Ins) {
      Bpl.BoundVariable bv = new Bpl.BoundVariable(p.Tok, new Bpl.TypedIdent(p.Tok, p.AssignUniqueName(f.IdGenerator), TrType(p.Type)));
      bvars.Add(bv);
      Bpl.Expr formal = new Bpl.IdentifierExpr(p.Tok, bv);
      f0args.Add(formal); f1args.Add(formal); f0argsCanCall.Add(formal); f1argsCanCall.Add(formal);
      Bpl.Expr wh = GetWhereClause(p.Tok, formal, p.Type, etran0, useAlloc);
      if (wh != null) { fwf0 = BplAnd(fwf0, wh); }
    }
    var canCall = new Bpl.FunctionCall(new Bpl.IdentifierExpr(f.Tok, f.FullSanitizedName + "#canCall", Bpl.Type.Bool));
    wellFormed = BplAnd(wellFormed, BplAnd(
      BplOr(new Bpl.NAryExpr(f.Tok, canCall, f0argsCanCall), fwf0),
      BplOr(new Bpl.NAryExpr(f.Tok, canCall, f1argsCanCall), fwf1)));

    /*
    DR: I conjecture that this should be enough,
        as the requires is preserved when the frame is:

    wellFormed = BplAnd(wellFormed,
      BplOr(new Bpl.NAryExpr(f.Tok, canCall, f0argsCanCall), fwf0));
    */

    var fn = new Bpl.FunctionCall(new Bpl.IdentifierExpr(f.Tok, f.FullSanitizedName, TrType(f.ResultType)));
    var F0 = new Bpl.NAryExpr(f.Tok, fn, f0args);
    var F1 = new Bpl.NAryExpr(f.Tok, fn, f1args);
    var eq = Bpl.Expr.Eq(F0, F1);
    var tr = new Bpl.Trigger(f.Tok, true, new List<Bpl.Expr> { h0IsHeapAnchor, heapSucc, F1 });

    var ax = new Bpl.ForallExpr(f.Tok, new List<Bpl.TypeVariable>(), bvars, null, tr,
      BplImp(BplAnd(wellFormed, BplAnd(h0IsHeapAnchor, heapSucc)),
      BplImp(q0, eq)));
    sink.AddTopLevelDeclaration(new Bpl.Axiom(f.Tok, ax, comment));
  }
}
