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
        var surrogate = new ThisSurrogate(f.Origin, ModuleResolver.GetReceiverType(f.Origin, f));
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
    BoundVariable bvPrevHeap = null;
    if (f is TwoStateFunction) {
      bvPrevHeap = new BoundVariable(f.Origin, new TypedIdent(f.Origin, "$prevHeap", Predef.HeapType));
      etran = new ExpressionTranslator(this, Predef,
        f.ReadsHeap ? new Bpl.IdentifierExpr(f.Origin, Predef.HeapVarName, Predef.HeapType) : null,
        new Bpl.IdentifierExpr(f.Origin, bvPrevHeap), f);
      etranHeap = etran;
    } else {
      etranHeap = new ExpressionTranslator(this, Predef, f.Origin, f);
      etran = readsHeap ? etranHeap : new ExpressionTranslator(this, Predef, (Expr)null, f);
    }

    // This method generates the Consequence Axiom, which has information about the function's
    // return type and postconditions.
    //
    // axiom  // consequence axiom
    //   (forall s, $Heap, formals ::                  // let args := $Heap,formals
    //       { f(s, args) }
    //       f#canCall(args)
    //       ==>
    //       ens &&
    //       OlderCondition &&
    //       f(s, args)-has-the-expected type);
    //
    // where:
    //
    // OlderCondition is added if the function has some 'older' parameters.
    //
    // Note, an antecedent $Heap[this,alloc] is intentionally left out:  including it would only weaken
    // the axiom.  Moreover, leaving it out does not introduce any soundness problem, because the Dafny
    // allocation statement changes only an allocation bit and then re-assumes $IsGoodHeap; so if it is
    // sound after that, then it would also have been sound just before the allocation.
    //
    List<Expr> tyargs;
    var formals = MkTyParamBinders(GetTypeParamsIncludingType(f), out tyargs);
    var args = new List<Expr>();
    var olderInParams = new List<Variable>(); // for use with older-condition
    BoundVariable layer;
    if (f.IsFuelAware()) {
      layer = new BoundVariable(f.Origin, new TypedIdent(f.Origin, "$ly", Predef.LayerType));
      formals.Add(layer);
      etran = etran.WithCustomFuelSetting(new CustomFuelSettings { { f, new FuelSetting(this, 0, new Bpl.IdentifierExpr(f.Origin, layer)) } });
      //etran = etran.WithLayer(new Bpl.IdentifierExpr(f.Tok, layer));
      // Note, "layer" is not added to "args" here; rather, that's done below, as needed
    } else {
      layer = null;
    }

    BoundVariable reveal;
    if (f.IsOpaque || f.IsMadeImplicitlyOpaque(options)) {
      reveal = new BoundVariable(f.Origin, new TypedIdent(f.Origin, "$reveal", Boogie.Type.Bool));
      formals.Add(reveal);
    } else {
      reveal = null;
    }

    if (f is TwoStateFunction) {
      Contract.Assert(bvPrevHeap != null);
      formals.Add(bvPrevHeap);
      args.Add(etran.Old.HeapExpr);
    }
    var bvHeap = new BoundVariable(f.Origin, new TypedIdent(f.Origin, Predef.HeapVarName, Predef.HeapType));
    if (f.ReadsHeap) {
      args.Add(new Bpl.IdentifierExpr(f.Origin, bvHeap));
    }
    // ante:  $IsGoodHeap($Heap) && $HeapSucc($prevHeap, $Heap) && this != null && formals-have-the-expected-types &&
    if (readsHeap) {
      formals.Add(bvHeap);
    }


    Expr parametersIsAlloc = Expr.True;
    Expr isExpr = null;
    if (!f.IsStatic) {
      var bvThis = new BoundVariable(f.Origin, new TypedIdent(f.Origin, etran.This, TrReceiverType(f)));
      formals.Add(bvThis);
      olderInParams.Add(bvThis);
      var bvThisIdExpr = new Bpl.IdentifierExpr(f.Origin, bvThis);
      args.Add(bvThisIdExpr);
      // add well-typedness conjunct to antecedent
      Type thisType = ModuleResolver.GetReceiverType(f.Origin, f);

      var expressionTranslator = f is TwoStateFunction ? etranHeap.Old : etranHeap;
      isExpr = GetWhereClause(f.Origin, bvThisIdExpr, thisType, expressionTranslator, IsAllocType.NOALLOC);

      var thisWhereClause = GetWhereClause(f.Origin, bvThisIdExpr, thisType, expressionTranslator,
        IsAllocType.ISALLOC, true);
      if (thisWhereClause != null) {
        parametersIsAlloc = BplAnd(parametersIsAlloc, thisWhereClause);
      }
    }
    foreach (Formal p in f.Ins) {
      var bv = new BoundVariable(p.Origin, new TypedIdent(p.Origin, p.AssignUniqueName(CurrentDeclaration.IdGenerator), TrType(p.Type)));
      Expr formal = new Bpl.IdentifierExpr(p.Origin, bv);
      formals.Add(bv);
      olderInParams.Add(bv);
      args.Add(formal);
      var wh = GetWhereClause(p.Origin, formal, p.Type, p.IsOld ? etranHeap.Old : etranHeap, ISALLOC);
      if (wh != null) {
        parametersIsAlloc = BplAnd(parametersIsAlloc, wh);
      }
    }

    var funcId = new Bpl.IdentifierExpr(f.Origin, f.FullSanitizedName, TrType(f.ResultType));
    var funcArgs = new List<Expr>();
    if (layer != null) {
      funcArgs.Add(new Bpl.IdentifierExpr(f.Origin, layer));
    }

    if (reveal != null) {
      funcArgs.Add(new Bpl.IdentifierExpr(f.Origin, reveal));
    }

    funcArgs.AddRange(args);
    Expr funcAppl = new NAryExpr(f.Origin, new FunctionCall(funcId), funcArgs);

    var canCallFuncId = new Bpl.IdentifierExpr(f.Origin, f.FullSanitizedName + "#canCall", Bpl.Type.Bool);
    var canCall = new NAryExpr(f.Origin, new FunctionCall(canCallFuncId), args);

    Expr post = Expr.True;
    // substitute function return value with the function call.
    var substMap = new Dictionary<IVariable, Expression>();
    if (f.Result != null) {
      substMap.Add(f.Result, new BoogieWrapper(funcAppl, f.ResultType));
    }
    foreach (AttributedExpression p in ens) {
      var bodyWithSubst = Substitute(p.E, null, substMap);
      var canCallEns = etran.CanCallAssumption(bodyWithSubst);
      post = BplAnd(post, canCallEns);
      var q = etran.TrExpr(bodyWithSubst);
      post = BplAnd(post, q);
    }
    var (olderParameterCount, olderCondition) = OlderCondition(f, funcAppl, olderInParams);
    if (olderParameterCount != 0) {
      post = BplAnd(post, olderCondition);
    }
    Expr whr = GetWhereClause(f.Origin, funcAppl, f.ResultType, etran, NOALLOC);
    if (whr != null) { post = BplAnd(post, whr); }

    if (RemoveLit(post) != Expr.True) {

      var axBody = BplImp(BplAnd(canCall, isExpr ?? Expr.True), post);
      Expr optionalHeap = readsHeap && !f.ReadsHeap ? etran.HeapExpr : null;

      var tr = BplTriggerHeap(this, f.Origin, funcAppl, optionalHeap, isExpr);
      var ax = BplForall(f.Origin, [], formals, null, tr, axBody);
      AddOtherDefinition(boogieFunction, new Axiom(f.Origin, ax, "consequence axiom for " + f.FullSanitizedName));
    }

    if (f.ResultType.MayInvolveReferences) {
      whr = GetWhereClause(f.Origin, funcAppl, f.ResultType, etranHeap, ISALLOC, true);
      Contract.Assert(whr != null); // since f.ResultType involves references, there should be an ISALLOC where clause
      if (whr != null) {
        Expr ante = canCall;
        if (readsHeap) {
          // all parameters are included in the CanCall, so that's the only antecedent we need
          Contract.Assert(formals.Contains(bvHeap));
        } else {
          // CanCall does not include the heap parameter but, since we will quantify over a heap, we need to
          // make sure the other parameters are connected to that heap
          Contract.Assert(f is not TwoStateFunction);
          ante = BplAnd(ante, parametersIsAlloc);
          formals = Cons(bvHeap, formals);
          var goodHeap = FunctionCall(f.Origin, BuiltinFunction.IsGoodHeap, null, etranHeap.HeapExpr);
          ante = BplAnd(ante, goodHeap);
        }

        var axBody = BplImp(ante, whr);
        var ax = BplForall(f.Origin, [], formals, null, BplTrigger(whr), axBody);
        var allocConsequenceAxiom = new Axiom(f.Origin, ax, "alloc consequence axiom for " + f.FullSanitizedName);
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
    Contract.Requires(Predef != null);
    Contract.Requires(f.EnclosingClass != null);
    Contract.Ensures((Contract.Result<Axiom>() == null) == (body == null)); // return null iff body is null

    // This method generates the Definition Axiom, suitably modified according to the optional "lits".
    //
    // axiom  // definition axiom
    //   (forall s, $Heap, formals ::                  // let args := $Heap,formals
    //       { f(Succ(s), args) }                      // (*)
    //       f#canCall(args)
    //       ==>
    //       BODY-can-make-its-calls &&
    //       f(Succ(s), args) == BODY);                // (*)
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
    BoundVariable bvPrevHeap = null;
    if (f is TwoStateFunction) {
      bvPrevHeap = new BoundVariable(f.Origin, new TypedIdent(f.Origin, "$prevHeap", Predef.HeapType));
      etran = new ExpressionTranslator(this, Predef,
        f.ReadsHeap ? new Bpl.IdentifierExpr(f.Origin, Predef.HeapVarName, Predef.HeapType) : null,
        new Bpl.IdentifierExpr(f.Origin, bvPrevHeap), f);
    } else {
      etran = f.ReadsHeap
        ? new ExpressionTranslator(this, Predef, f.Origin, f)
        : new ExpressionTranslator(this, Predef, readsHeap ? NewOneHeapExpr(f.Origin) : null, f);
    }

    // quantify over the type arguments, and add them first to the arguments
    List<Expr> args = [];
    List<Expr> tyargs = GetTypeArguments(f, null).ConvertAll(TypeToTy);

    var forallFormals = MkTyParamBinders(GetTypeParamsIncludingType(f), out _);
    List<Variable> funcFormals = [];
    var reqFuncArguments = new List<Expr>();

    BoundVariable layer;
    BoundVariable reveal;
    if (f.IsFuelAware()) {
      layer = new BoundVariable(f.Origin, new TypedIdent(f.Origin, "$ly", Predef.LayerType));
      forallFormals.Add(layer);
      funcFormals.Add(layer);
      reqFuncArguments.Add(new Bpl.IdentifierExpr(f.Origin, layer));
      // Note, "layer" is not added to "args" here; rather, that's done below, as needed
    } else {
      layer = null;
    }

    if (f.IsOpaque || f.IsMadeImplicitlyOpaque(options)) {
      reveal = new BoundVariable(f.Origin, new TypedIdent(f.Origin, "$reveal", Boogie.Type.Bool));
      //funcFormals.Add(reveal);
      //reqFuncArguments.Add(new Bpl.IdentifierExpr(f.Tok, reveal));
      // Note, "reveal" is not added to "args" here; rather, that's done below, as needed
    } else {
      reveal = null;
    }

    Expr ante = Expr.True;
    if (f is TwoStateFunction) {
      Contract.Assert(bvPrevHeap != null);
      forallFormals.Add(bvPrevHeap);
      funcFormals.Add(bvPrevHeap);
      args.Add(etran.Old.HeapExpr);
      reqFuncArguments.Add(new Bpl.IdentifierExpr(f.Origin, bvPrevHeap));
      // ante:  $IsGoodHeap($prevHeap) &&
      ante = BplAnd(ante, FunctionCall(f.Origin, BuiltinFunction.IsGoodHeap, null, etran.Old.HeapExpr));
    }

    if (f.ReadsHeap) {
      var bv = new BoundVariable(f.Origin, new TypedIdent(f.Origin, Predef.HeapVarName, Predef.HeapType));
      funcFormals.Add(bv);
      args.Add(new Bpl.IdentifierExpr(f.Origin, bv));
      reqFuncArguments.Add(new Bpl.IdentifierExpr(f.Origin, bv));

      // ante:  $IsGoodHeap($Heap) && $HeapSucc($prevHeap, $Heap) && this != null && formals-have-the-expected-types &&
      forallFormals.Add(bv);
      var goodHeap = FunctionCall(f.Origin, BuiltinFunction.IsGoodHeap, null, etran.HeapExpr);
      ante = BplAnd(ante, goodHeap);
      if (f is TwoStateFunction) {
        ante = BplAnd(ante, HeapSucc(etran.Old.HeapExpr, etran.HeapExpr));
      }
    }

    // ante:  conditions on bounded type parameters
    foreach (var typeBoundAxiom in TypeBoundAxioms(f.Origin, Concat(f.EnclosingClass.TypeArgs, f.TypeArgs))) {
      ante = BplAnd(ante, typeBoundAxiom);
    }

    // Expr isType = null;
    Expression receiverReplacement = null;
    if (!f.IsStatic) {
      var bvThis = new BoundVariable(f.Origin, new TypedIdent(f.Origin, etran.This, TrReceiverType(f)));
      forallFormals.Add(bvThis);
      funcFormals.Add(bvThis);
      reqFuncArguments.Add(new Bpl.IdentifierExpr(f.Origin, bvThis));
      var bvThisIdExpr = new Bpl.IdentifierExpr(f.Origin, bvThis);
      if (lits != null && lits.Exists(p => p is ThisSurrogate)) {
        args.Add(Lit(bvThisIdExpr));
        var th = new ThisExpr(f);
        var l = new UnaryOpExpr(f.Origin, UnaryOpExpr.Opcode.Lit, th) {
          Type = th.Type
        };
        receiverReplacement = l;
      } else {
        args.Add(bvThisIdExpr);
      }

      // add well-typedness conjunct to antecedent
      Type thisType = ModuleResolver.GetReceiverType(f.Origin, f);
      var expressionTranslator = (f is TwoStateFunction ? etran.Old : etran);
      // isType = GetWhereClause(f.Origin, bvThisIdExpr, thisType, expressionTranslator, NOALLOC);
      Expr wh = BplAnd(
        ReceiverNotNull(bvThisIdExpr),
        expressionTranslator.GoodRef(f.Origin, bvThisIdExpr, thisType));
      ante = BplAnd(ante, wh);
    }

    var typeMap = new Dictionary<TypeParameter, Type>();
    var anteReqAxiom = ante; // note that antecedent so far is the same for #requires axioms, even the receiver parameter of a two-state function
    var substMap = new Dictionary<IVariable, Expression>();
    foreach (Formal p in f.Ins) {
      var pType = p.Type.Subst(typeMap);
      var bv = new BoundVariable(p.Origin,
        new TypedIdent(p.Origin, p.AssignUniqueName(CurrentDeclaration.IdGenerator), TrType(pType)));
      forallFormals.Add(bv);
      funcFormals.Add(bv);
      reqFuncArguments.Add(new Bpl.IdentifierExpr(f.Origin, bv));
      Expr formal = new Bpl.IdentifierExpr(p.Origin, bv);
      if (lits != null && lits.Contains(p) && !substMap.ContainsKey(p)) {
        args.Add(Lit(formal));
        var ie = new IdentifierExpr(p.Origin, p.AssignUniqueName(f.IdGenerator));
        ie.Var = p;
        ie.Type = ie.Var.Type;
        var l = new UnaryOpExpr(p.Origin, UnaryOpExpr.Opcode.Lit, ie);
        l.Type = ie.Var.Type;
        substMap.Add(p, l);
      } else {
        args.Add(formal);
      }

      // add well-typedness conjunct to antecedent
      Expr wh = GetWhereClause(p.Origin, formal, pType, p.IsOld ? etran.Old : etran, NOALLOC);
      if (wh != null) {
        ante = BplAnd(ante, wh);
      }

      wh = GetWhereClause(p.Origin, formal, pType, etran, NOALLOC);
      if (wh != null) {
        anteReqAxiom = BplAnd(anteReqAxiom, wh);
      }
    }

    Expr pre = Expr.True;
    foreach (AttributedExpression req in ConjunctsOf(f.Req)) {
      pre = BplAnd(pre, etran.TrExpr(Substitute(req.E, receiverReplacement, substMap)));
    }

    var preReqAxiom = pre;
    if (f is TwoStateFunction) {
      // Checked preconditions that old parameters really existed in previous state
      var index = 0;
      Expr preRa = Expr.True;
      foreach (var formal in f.Ins) {
        if (formal.IsOld) {
          var dafnyFormalIdExpr = new IdentifierExpr(formal.Origin, formal);
          preRa = BplAnd(preRa, MkIsAlloc(etran.TrExpr(dafnyFormalIdExpr), formal.Type, etran.Old.HeapExpr));
        }

        index++;
      }

      preReqAxiom = BplAnd(preRa, pre);
    }

    var canCallFuncId = new Bpl.IdentifierExpr(f.Origin, f.FullSanitizedName + "#canCall", Bpl.Type.Bool);
    var useViaCanCall = new NAryExpr(f.Origin, new FunctionCall(canCallFuncId), args);

    // Add the precondition function and its axiom (which is equivalent to the anteReqAxiom)
    if (body == null || (RevealedInScope(f) && lits == null)) {
      var precondF = new Bpl.Function(f.Origin,
        RequiresName(f), [],
        funcFormals.ConvertAll(v => (Variable)BplFormalVar(null, v.TypedIdent.Type, true)),
        BplFormalVar(null, Bpl.Type.Bool, false));
      sink.AddTopLevelDeclaration(precondF);

      var appl = FunctionCall(f.Origin, RequiresName(f), Bpl.Type.Bool, reqFuncArguments);
      Trigger trig1 = BplTriggerHeap(this, f.Origin, appl, f.ReadsHeap ? etran.HeapExpr : null/*, isType*/);
      // axiom (forall params :: { f#requires(params) }  ante ==> f#requires(params) == pre);
      AddOtherDefinition(precondF, new Axiom(f.Origin,
        BplForall(forallFormals, trig1, BplImp(anteReqAxiom, Expr.Eq(appl, preReqAxiom))),
        "#requires axiom for " + f.FullSanitizedName));

      Trigger trig2 = BplTriggerHeap(this, f.Origin, appl, f.ReadsHeap ? etran.HeapExpr : null, null);
      AddOtherDefinition(precondF, new Axiom(f.Origin,
        BplForall(f.Origin, [], forallFormals, null, trig2, Expr.Imp(appl, useViaCanCall)),
        "#requires ==> #canCall for " + f.FullSanitizedName));
    }

    if (body == null || !RevealedInScope(f)) {
      return null;
    }

    // useViaCanCall: f#canCall(args)
    ante = useViaCanCall;

    var funcId = new Bpl.IdentifierExpr(f.Origin, f.FullSanitizedName, TrType(f.ResultType));
    var funcArgs = new List<Expr>();
    if (layer != null) {
      var ly = new Bpl.IdentifierExpr(f.Origin, layer);
      //if (lits == null) {
      funcArgs.Add(LayerSucc(ly));
      //} else {
      //  funcArgs.Add(ly);
      //}
    }

    if (reveal != null) {
      funcArgs.Add(new Bpl.LiteralExpr(f.Origin, true));
    }

    funcArgs.AddRange(args);
    Expr funcAppl = new NAryExpr(f.Origin, new FunctionCall(funcId), funcArgs);

    Trigger tr = BplTriggerHeap(this, f.Origin, funcAppl, f.ReadsHeap ? etran.HeapExpr : null);
    Expr tastyVegetarianOption; // a.k.a. the "meat" of the operation :)
    if (!RevealedInScope(f)) {
      tastyVegetarianOption = Expr.True;
    } else {
      var bodyWithSubst = Substitute(body, receiverReplacement, substMap);
      if (f is PrefixPredicate) {
        var pp = (PrefixPredicate)f;
        bodyWithSubst = PrefixSubstitution(pp, bodyWithSubst);
      }

      Expr ly = null;
      if (layer != null) {
        ly = new Bpl.IdentifierExpr(f.Origin, layer);
        if (lits != null) {
          // Lit axiom doesn't consume any fuel
          ly = LayerSucc(ly);
        }
      }

      var etranBody = layer == null ? etran : etran.LimitedFunctions(f, ly);
      var trbody = AdaptBoxing(f.Origin, etranBody.TrExpr(bodyWithSubst), f.Body.Type, f.ResultType);
      tastyVegetarianOption = BplAnd(etranBody.CanCallAssumption(bodyWithSubst),
        BplAnd(TrFunctionSideEffect(bodyWithSubst, etranBody), Expr.Eq(funcAppl, trbody)));
    }

    QKeyValue kv = null;
    if (lits != null) {
      kv = new QKeyValue(f.Origin, "weight", new List<object>() { Expr.Literal(3) }, null);
    }

    Expr ax = BplForall(f.Origin, [], forallFormals, kv, tr,
      BplImp(ante, tastyVegetarianOption));
    var comment = "definition axiom for " + f.FullSanitizedName;
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
    var axe = new Axiom(f.Origin, ax, comment) {
      CanHide = true
    };
    if (proofDependencies == null) {
      return axe;
    }

    proofDependencies.SetCurrentDefinition(f.FullSanitizedName, f);
    proofDependencies.AddProofDependencyId(axe, f.Origin, new FunctionDefinitionDependency(f));
    return axe;
  }


  Expr TrFunctionSideEffect(Expression expr, ExpressionTranslator etran) {
    Expr e = Expr.True;
    if (expr is StmtExpr) {
      // if there is a call to reveal_ lemma, we need to record its side effect.
      var stmt = ((StmtExpr)expr).S;
      e = TrFunctionSideEffect(stmt, etran);
    }
    return e;
  }

  Expr TrFunctionSideEffect(Statement stmt, ExpressionTranslator etran) {
    Expr e = Expr.True;
    e = TrStmtSideEffect(e, stmt, etran);
    foreach (var ss in stmt.SubStatements) {
      e = TrStmtSideEffect(e, ss, etran);
    }
    return e;
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
    Expr prevH = null;
    BoundVariable prevHVar = null;
    Expr reveal = null;
    BoundVariable revealVar = null;
    if (f.IsOpaque || f.IsMadeImplicitlyOpaque(options)) {
      revealVar = BplBoundVar("$reveal", Bpl.Type.Bool, out reveal);
    }
    if (f is TwoStateFunction) {
      // The previous-heap argument is the same for both function arguments.  That is,
      // the frame axiom says nothing about functions invoked with different previous heaps.
      prevHVar = BplBoundVar("$prevHeap", Predef.HeapType, out prevH);
    }
    Expr h0; var h0Var = BplBoundVar("$h0", Predef.HeapType, out h0);
    Expr h1; var h1Var = BplBoundVar("$h1", Predef.HeapType, out h1);

    var etran0 = new ExpressionTranslator(this, Predef, h0, f);
    var etran1 = new ExpressionTranslator(this, Predef, h1, f);

    Expr wellFormed = BplAnd(
      FunctionCall(f.Origin, BuiltinFunction.IsGoodHeap, null, etran0.HeapExpr),
      FunctionCall(f.Origin, BuiltinFunction.IsGoodHeap, null, etran1.HeapExpr));

    Expr o; var oVar = BplBoundVar("$o", Predef.RefType, out o);
    Expr field; var fieldVar = BplBoundVar("$f", Predef.FieldName(f.Origin), out field);
    Expr oNotNull = Expr.Neq(o, Predef.Null);
    Expr oNotNullAlloced = oNotNull;
    Expr unchanged = Expr.Eq(ReadHeap(f.Origin, h0, o, field), ReadHeap(f.Origin, h1, o, field));

    Expr h0IsHeapAnchor = FunctionCall(h0.tok, BuiltinFunction.IsHeapAnchor, null, h0);
    Expr heapSucc = HeapSucc(h0, h1);
    Expr r0 = InRWClause(f.Origin, o, field, f.Reads.Expressions, etran0, null, null);
    Expr q0 = new Bpl.ForallExpr(f.Origin, [], [oVar, fieldVar],
      BplImp(BplAnd(oNotNullAlloced, r0), unchanged));

    var bForallVars = MkTyParamBinders(GetTypeParamsIncludingType(f), out _);
    var f0Args = new List<Expr>();
    var f1Args = new List<Expr>();
    var f0ArgsCanCall = new List<Expr>();
    var f1ArgsCanCall = new List<Expr>();
    if (f.IsFuelAware()) {
      Expr s; var sV = BplBoundVar("$ly", Predef.LayerType, out s);
      bForallVars.Add(sV);
      f0Args.Add(s); f1Args.Add(s);  // but don't add to f0argsCanCall or f1argsCanCall
    }

    if (reveal != null) {
      bForallVars.Add(revealVar);
      f0Args.Add(reveal); f1Args.Add(reveal);
    }

    if (prevH != null) {
      bForallVars.Add(prevHVar);
      f0Args.Add(prevH); f1Args.Add(prevH); f0ArgsCanCall.Add(prevH); f1ArgsCanCall.Add(prevH);
    }
    bForallVars.Add(h0Var); bForallVars.Add(h1Var);
    f0Args.Add(h0); f1Args.Add(h1); f0ArgsCanCall.Add(h0); f1ArgsCanCall.Add(h1);

    Expr whereClause = null;
    var useAlloc = f.Reads.Expressions.Exists(fe => fe.E is WildcardExpr) ? ISALLOC : NOALLOC;
    if (!f.IsStatic) {
      var thVar = BplBoundVar("this", TrReceiverType(f), out var th);
      bForallVars.Add(thVar);
      f0Args.Add(th); f1Args.Add(th); f0ArgsCanCall.Add(th); f1ArgsCanCall.Add(th);

      Type thisType = ModuleResolver.GetReceiverType(f.Origin, f);
      whereClause = GetWhereClause(f.Origin, th, thisType, etran0, useAlloc);
      Expr wh = BplAnd(ReceiverNotNull(th), whereClause);
      wellFormed = BplAnd(wellFormed, wh);
    }

    // (formalsAreWellFormed[h0] || canCallF(h0,...)) && (formalsAreWellFormed[h1] || canCallF(h1,...))
    Expr fwf0 = Expr.True;
    Expr fwf1 = Expr.True;
    foreach (Formal p in f.Ins) {
      BoundVariable bv = new BoundVariable(p.Origin, new TypedIdent(p.Origin, p.AssignUniqueName(f.IdGenerator), TrType(p.Type)));
      bForallVars.Add(bv);
      Expr formal = new Bpl.IdentifierExpr(p.Origin, bv);
      f0Args.Add(formal); f1Args.Add(formal); f0ArgsCanCall.Add(formal); f1ArgsCanCall.Add(formal);
      Expr wh = GetWhereClause(p.Origin, formal, p.Type, etran0, useAlloc);
      if (wh != null) {
        fwf0 = BplAnd(fwf0, wh);
      }
      wh = GetWhereClause(p.Origin, formal, p.Type, etran1, useAlloc);
      if (wh != null) {
        fwf1 = BplAnd(fwf1, wh);
      }
    }
    var canCall = new FunctionCall(new Bpl.IdentifierExpr(f.Origin, f.FullSanitizedName + "#canCall", Bpl.Type.Bool));
    var f0CanCall = new NAryExpr(f.Origin, canCall, f0ArgsCanCall);
    var f1CanCall = new NAryExpr(f.Origin, canCall, f1ArgsCanCall);
    wellFormed = BplAnd(wellFormed, Expr.Or(
      BplOr(f0CanCall, fwf0),
      BplOr(f1CanCall, fwf1)));
    /*
    JA: I conjecture that we don't need fwf0 or fwf1 here. But, we
        will need both can calls,
        i.e.,
        wellFormed = BplAnd(wellFormed, BplOr(f0canCall, f1canCall))
    */
    /*
    DR: I conjecture that this should be enough,
        as the requires is preserved when the frame is:

    wellFormed = BplAnd(wellFormed,
      BplOr(new Bpl.NAryExpr(f.Tok, canCall, f0argsCanCall), fwf0));
    */

    var fn = new FunctionCall(new Bpl.IdentifierExpr(f.Origin, f.FullSanitizedName, TrType(f.ResultType)));
    var f0 = new NAryExpr(f.Origin, fn, f0Args);
    var f1 = new NAryExpr(f.Origin, fn, f1Args);
    var eq = BplAnd(Expr.Eq(f0, f1), Expr.Eq(f0CanCall, f1CanCall));
    var tr = new Trigger(f.Origin, true,
      new List<Expr> { h0IsHeapAnchor, heapSucc, f1, whereClause }.Where(t => t != null));

    var ax = new Bpl.ForallExpr(f.Origin, [], bForallVars, null, tr,
      BplImp(BplAnd(wellFormed, BplAnd(h0IsHeapAnchor, heapSucc)),
      BplImp(q0, eq)));
    sink.AddTopLevelDeclaration(new Axiom(f.Origin, ax, comment));
  }
}
