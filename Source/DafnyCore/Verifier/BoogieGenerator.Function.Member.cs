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

  private void AddClassMember_Function(Function f) {
    Contract.Ensures(currentModule == null && codeContext == null);
    Contract.Ensures(currentModule == null && codeContext == null);

    currentModule = f.EnclosingClass.EnclosingModuleDefinition;
    codeContext = f;

    // declare function
    var boogieFunction = GetOrCreateFunction(f);
    // add synonym axiom
    if (f.IsFuelAware()) {
      AddFuelSuccSynonymAxiom(f);
      AddFuelZeroSynonymAxiom(f);
    }
    // add frame axiom
    if (f.ReadsHeap) {
      AddFrameAxiom(f);
    }
    // add consequence axiom
    AddFunctionConsequenceAxiom(boogieFunction, f, f.Ens);
    // add definition axioms, suitably specialized for literals
    if (f.Body != null && RevealedInScope(f)) {
      AddFunctionAxiom(boogieFunction, f, f.Body.Resolved);
    } else {
      // for body-less functions, at least generate its #requires function
      var b = GetFunctionAxiom(f, null, null);
      Contract.Assert(b == null);
    }
    // for a function in a class C that overrides a function in a trait J, add an axiom that connects J.F and C.F
    if (f.OverriddenFunction != null) {
      sink.AddTopLevelDeclaration(FunctionOverrideAxiom(f.OverriddenFunction, f));
    }

    // supply the connection between least/greatest predicates and prefix predicates
    if (f is ExtremePredicate) {
      AddPrefixPredicateAxioms(((ExtremePredicate)f).PrefixPredicate);
    }

    Reset();
  }

  void AddFuelSuccSynonymAxiom(Function f, bool forHandle = false) {
    Contract.Requires(f != null);
    Contract.Requires(f.IsFuelAware());
    Contract.Requires(sink != null && Predef != null);
    // axiom  // layer synonym axiom
    //   (forall s, $Heap, formals ::
    //       { f(Succ(s), $Heap, formals) }
    //       f(Succ(s), $Heap, formals) == f(s, $Heap, formals));

    var forallFormals = MkTyParamBinders(GetTypeParamsIncludingType(f), out _);
    var args1 = new List<Bpl.Expr>();
    var args0 = new List<Bpl.Expr>();

    var bv = new Bpl.BoundVariable(f.Origin, new Bpl.TypedIdent(f.Origin, "$ly", Predef.LayerType));
    forallFormals.Add(bv);
    var s = new Bpl.IdentifierExpr(f.Origin, bv);
    args1.Add(FunctionCall(f.Origin, BuiltinFunction.LayerSucc, null, s));
    args0.Add(s);
    if (f.IsOpaque || f.IsMadeImplicitlyOpaque(options)) {
      var bvReveal = new Bpl.BoundVariable(f.Origin, new Bpl.TypedIdent(f.Origin, "$reveal", Boogie.Type.Bool));
      forallFormals.Add(bvReveal);
      var sReveal = new Bpl.IdentifierExpr(f.Origin, bvReveal);
      args1.Add(sReveal);
      args0.Add(sReveal);
    }

    if (f is TwoStateFunction) {
      bv = new Bpl.BoundVariable(f.Origin, new Bpl.TypedIdent(f.Origin, "$prevHeap", Predef.HeapType));
      forallFormals.Add(bv);
      s = new Bpl.IdentifierExpr(f.Origin, bv);
      args1.Add(s);
      args0.Add(s);
    }
    if (!forHandle && f.ReadsHeap) {
      bv = new Bpl.BoundVariable(f.Origin, new Bpl.TypedIdent(f.Origin, Predef.HeapVarName, Predef.HeapType));
      forallFormals.Add(bv);
      s = new Bpl.IdentifierExpr(f.Origin, bv);
      args1.Add(s);
      args0.Add(s);
    }

    if (!f.IsStatic) {
      bv = new Bpl.BoundVariable(f.Origin, new Bpl.TypedIdent(f.Origin, "this", TrReceiverType(f)));
      forallFormals.Add(bv);
      s = new Bpl.IdentifierExpr(f.Origin, bv);
      args1.Add(s);
      args0.Add(s);
    }
    if (!forHandle) {
      foreach (var p in f.Ins) {
        bv = new Bpl.BoundVariable(p.Origin, new Bpl.TypedIdent(p.Origin, p.AssignUniqueName(f.IdGenerator), TrType(p.Type)));
        forallFormals.Add(bv);
        s = new Bpl.IdentifierExpr(f.Origin, bv);
        args1.Add(s);
        args0.Add(s);
      }
    }

    var name = forHandle ? f.FullSanitizedName + "#Handle" : f.FullSanitizedName;
    var funcID = new Bpl.FunctionCall(new Bpl.IdentifierExpr(f.Origin, name, TrType(f.ResultType)));
    var funcAppl1 = new Bpl.NAryExpr(f.Origin, funcID, args1);
    var funcAppl0 = new Bpl.NAryExpr(f.Origin, funcID, args0);

    Bpl.Trigger tr = new Bpl.Trigger(f.Origin, true, new List<Bpl.Expr> { funcAppl1 });
    Bpl.Expr ax = new Bpl.ForallExpr(f.Origin, [], forallFormals, null, tr, Bpl.Expr.Eq(funcAppl1, funcAppl0));
    AddOtherDefinition(GetOrCreateFunction(f), new Bpl.Axiom(f.Origin, ax, "layer synonym axiom"));
  }

  void AddFuelZeroSynonymAxiom(Function f) {
    // axiom  // fuel axiom
    //   (forall s, $Heap, formals ::
    //       { f(AsFuelBottom(s), $Heap, formals) }
    //       f(s, $Heap, formals) == f($LZ, $Heap, formals));
    Contract.Requires(f != null);
    Contract.Requires(f.IsFuelAware());
    Contract.Requires(sink != null && Predef != null);

    var forallFormals = MkTyParamBinders(GetTypeParamsIncludingType(f), out _);
    var args2 = new List<Bpl.Expr>();
    var args1 = new List<Bpl.Expr>();
    var args0 = new List<Bpl.Expr>();

    var bv = new Bpl.BoundVariable(f.Origin, new Bpl.TypedIdent(f.Origin, "$ly", Predef.LayerType));
    forallFormals.Add(bv);
    var s = new Bpl.IdentifierExpr(f.Origin, bv);
    args2.Add(FunctionCall(f.Origin, BuiltinFunction.AsFuelBottom, null, s));
    args1.Add(s);
    args0.Add(new Bpl.IdentifierExpr(f.Origin, "$LZ", Predef.LayerType)); // $LZ
    if (f.IsOpaque || f.IsMadeImplicitlyOpaque(options)) {
      var bvReveal = new Bpl.BoundVariable(f.Origin, new Bpl.TypedIdent(f.Origin, "$reveal", Boogie.Type.Bool));
      forallFormals.Add(bvReveal);
      var sReveal = new Bpl.IdentifierExpr(f.Origin, bvReveal);
      args2.Add(sReveal);
      args1.Add(sReveal);
      args0.Add(sReveal);
    }

    if (f is TwoStateFunction) {
      bv = new Bpl.BoundVariable(f.Origin, new Bpl.TypedIdent(f.Origin, "$prevHeap", Predef.HeapType));
      forallFormals.Add(bv);
      s = new Bpl.IdentifierExpr(f.Origin, bv);
      args2.Add(s);
      args1.Add(s);
      args0.Add(s);
    }
    if (f.ReadsHeap) {
      bv = new Bpl.BoundVariable(f.Origin, new Bpl.TypedIdent(f.Origin, Predef.HeapVarName, Predef.HeapType));
      forallFormals.Add(bv);
      s = new Bpl.IdentifierExpr(f.Origin, bv);
      args2.Add(s);
      args1.Add(s);
      args0.Add(s);
    }

    if (!f.IsStatic) {
      bv = new Bpl.BoundVariable(f.Origin, new Bpl.TypedIdent(f.Origin, "this", TrReceiverType(f)));
      forallFormals.Add(bv);
      s = new Bpl.IdentifierExpr(f.Origin, bv);
      args2.Add(s);
      args1.Add(s);
      args0.Add(s);
    }
    foreach (var p in f.Ins) {
      bv = new Bpl.BoundVariable(p.Origin, new Bpl.TypedIdent(p.Origin, p.AssignUniqueName(f.IdGenerator), TrType(p.Type)));
      forallFormals.Add(bv);
      s = new Bpl.IdentifierExpr(f.Origin, bv);
      args2.Add(s);
      args1.Add(s);
      args0.Add(s);
    }

    var funcID = new Bpl.FunctionCall(new Bpl.IdentifierExpr(f.Origin, f.FullSanitizedName, TrType(f.ResultType)));
    var funcAppl2 = new Bpl.NAryExpr(f.Origin, funcID, args2);
    var funcAppl1 = new Bpl.NAryExpr(f.Origin, funcID, args1);
    var funcAppl0 = new Bpl.NAryExpr(f.Origin, funcID, args0);

    Bpl.Trigger tr = new Bpl.Trigger(f.Origin, true, new List<Bpl.Expr> { funcAppl2 });
    Bpl.Expr ax = new Bpl.ForallExpr(f.Origin, [], forallFormals, null, tr, Bpl.Expr.Eq(funcAppl1, funcAppl0));
    AddOtherDefinition(GetOrCreateFunction(f), (new Bpl.Axiom(f.Origin, ax, "fuel synonym axiom")));
  }


  /// <summary>
  /// Essentially, the function override axiom looks like:
  ///   axiom (forall $heap: HeapType, typeArgs: Ty, this: ref, x#0: int, fuel: LayerType ::
  ///     { J.F(fuel, $heap, G(typeArgs), this, x#0), C.F(fuel, $heap, typeArgs, this, x#0) }
  ///     { J.F(fuel, $heap, G(typeArgs), this, x#0), $Is(this, C) }
  ///     C.F#canCall(args) || (J.F#canCall(args) && $Is(this, C))
  ///     ==>
  ///     (J.F#canCall(args) ==> C.F#canCall(args)) &&
  ///     J.F(fuel, $heap, G(typeArgs), this, x#0) == C.F(fuel, $heap, typeArgs, this, x#0));
  /// (without the other usual antecedents).  Essentially, the override gives a part of the body of the
  /// trait's function, so we call FunctionAxiom to generate a conditional axiom (that is, we pass in the "overridingFunction"
  /// parameter to FunctionAxiom, which will add 'dtype(this) == class.C' as an additional antecedent) for a
  /// body of 'C.F(this, x#0)'.
  /// </summary>
  private Boogie.Axiom FunctionOverrideAxiom(Function f, Function overridingFunction) {
    Contract.Requires(f != null);
    Contract.Requires(overridingFunction != null);
    Contract.Requires(Predef != null);
    Contract.Requires(f.EnclosingClass != null);
    Contract.Requires(!f.IsStatic);
    Contract.Requires(overridingFunction.EnclosingClass is TopLevelDeclWithMembers);
    Contract.Ensures(Contract.Result<Boogie.Axiom>() != null);

    bool readsHeap = f.ReadsHeap || overridingFunction.ReadsHeap;

    ExpressionTranslator etran;
    Boogie.BoundVariable bvPrevHeap = null;
    if (f is TwoStateFunction) {
      bvPrevHeap = new Boogie.BoundVariable(f.Origin, new Boogie.TypedIdent(f.Origin, "$prevHeap", Predef.HeapType));
      etran = new ExpressionTranslator(this, Predef,
        f.ReadsHeap ? new Boogie.IdentifierExpr(f.Origin, Predef.HeapVarName, Predef.HeapType) : null,
        new Boogie.IdentifierExpr(f.Origin, bvPrevHeap),
        f);
    } else if (readsHeap) {
      etran = new ExpressionTranslator(this, Predef, f.Origin, f);
    } else {
      etran = new ExpressionTranslator(this, Predef, (Boogie.Expr)null, f);
    }


    // "forallFormals" is built to hold the bound variables of the quantification
    // argsJF are the arguments to J.F (the function in the trait)
    // argsCF are the arguments to C.F (the overriding function)
    List<Variable> forallFormals = [];
    List<Expr> argsJf = [];
    List<Expr> argsJfCanCall = [];
    List<Expr> argsCf = [];
    IReadOnlyList<Expr> argsCfCanCall = new List<Expr>();

    // Add type arguments
    forallFormals.AddRange(MkTyParamBinders(GetTypeParamsIncludingType(overridingFunction), out _));
    var typeArguments = GetTypeArguments(f, overridingFunction).ConvertAll(TypeToTy);
    // argsJfCanCall.AddRange(typeArguments);
    typeArguments = GetTypeArguments(overridingFunction, null).ConvertAll(TypeToTy);
    // argsCfCanCall = argsCfCanCall.Concat(typeArguments);

    var moreArgsJF = new List<Boogie.Expr>(); // non-type-parameters, non-fuel, non-reveal arguments
    var moreArgsCF = new List<Boogie.Expr>(); // non-type-parameters, non-fuel, non-reveal arguments
    Expr layer = null;
    Expr reveal = null;

    // Add the fuel argument
    if (f.IsFuelAware()) {
      Contract.Assert(overridingFunction.IsFuelAware());  // f.IsFuelAware() ==> overridingFunction.IsFuelAware()
      var fuel = new Boogie.BoundVariable(f.Origin, new Boogie.TypedIdent(f.Origin, "$fuel", Predef.LayerType));
      forallFormals.Add(fuel);
      layer = new Boogie.IdentifierExpr(f.Origin, fuel);
      argsJf.Add(layer);
    } else if (overridingFunction.IsFuelAware()) {
      // We can't use a bound variable $fuel, because then one of the triggers won't be mentioning this $fuel.
      // Instead, we do the next best thing: use the literal $LZ.
      layer = new Boogie.IdentifierExpr(f.Origin, "$LZ", Predef.LayerType); // $LZ
    }

    if (f.IsOpaque || f.IsMadeImplicitlyOpaque(options)) {
      Contract.Assert(overridingFunction.IsOpaque || options.Get(CommonOptionBag.DefaultFunctionOpacity) == CommonOptionBag.DefaultFunctionOpacityOptions.Opaque || options.Get(CommonOptionBag.DefaultFunctionOpacity) == CommonOptionBag.DefaultFunctionOpacityOptions.AutoRevealDependencies);
      var revealVar = new Boogie.BoundVariable(f.Origin, new Boogie.TypedIdent(f.Origin, "reveal", Boogie.Type.Bool));
      forallFormals.Add(revealVar);
      reveal = new Boogie.IdentifierExpr(f.Origin, revealVar);
      argsJf.Add(reveal);
    } else if (overridingFunction.IsOpaque || overridingFunction.IsMadeImplicitlyOpaque(options)) {
      reveal = GetRevealConstant(overridingFunction);
    }

    // Add heap arguments
    if (f is TwoStateFunction) {
      Contract.Assert(bvPrevHeap != null);
      forallFormals.Add(bvPrevHeap);
      moreArgsJF.Add(etran.Old.HeapExpr);
      moreArgsCF.Add(etran.Old.HeapExpr);
    }
    if (f.ReadsHeap || overridingFunction.ReadsHeap) {
      var heap = new Boogie.BoundVariable(f.Origin, new Boogie.TypedIdent(f.Origin, Predef.HeapVarName, Predef.HeapType));
      forallFormals.Add(heap);
      if (f.ReadsHeap) {
        moreArgsJF.Add(new Boogie.IdentifierExpr(f.Origin, heap));
      }
      if (overridingFunction.ReadsHeap) {
        moreArgsCF.Add(new Boogie.IdentifierExpr(overridingFunction.Origin, heap));
      }
    }

    // Add receiver parameter
    Type thisType = ModuleResolver.GetReceiverType(f.Origin, overridingFunction);
    var bvThis = new Boogie.BoundVariable(f.Origin, new Boogie.TypedIdent(f.Origin, etran.This, TrType(thisType)));
    forallFormals.Add(bvThis);
    var bvThisExpr = new Boogie.IdentifierExpr(f.Origin, bvThis);
    moreArgsJF.Add(BoxifyForTraitParent(f.Origin, bvThisExpr, f, thisType));
    moreArgsCF.Add(bvThisExpr);
    // $Is(this, C)
    var isOfSubtype = GetWhereClause(overridingFunction.Origin, bvThisExpr, thisType, f is TwoStateFunction ? etran.Old : etran,
      IsAllocType.NEVERALLOC, alwaysUseSymbolicName: true);

    // Add other arguments
    var typeMap = GetTypeArgumentSubstitutionMap(f, overridingFunction);
    foreach (Formal p in f.Ins) {
      var pType = p.Type.Subst(typeMap);
      var bv = new Boogie.BoundVariable(p.Origin, new Boogie.TypedIdent(p.Origin, p.AssignUniqueName(CurrentDeclaration.IdGenerator), TrType(pType)));
      forallFormals.Add(bv);
      var jfArg = new Boogie.IdentifierExpr(p.Origin, bv);
      moreArgsJF.Add(ModeledAsBoxType(p.Type) ? BoxIfNotNormallyBoxed(p.Origin, jfArg, pType) : jfArg);
      moreArgsCF.Add(new Boogie.IdentifierExpr(p.Origin, bv));
    }

    if (layer != null) {
      argsCf.Add(layer);
    }

    if (reveal != null) {
      argsCf.Add(reveal);
    }

    argsJf = Concat(argsJf, moreArgsJF);
    argsJfCanCall = Concat(argsJfCanCall, moreArgsJF);
    argsCf = Concat(argsCf, moreArgsCF);
    argsCfCanCall = argsCfCanCall.Concat(moreArgsCF);

    Bpl.Expr canCallFunc, canCallOverridingFunc;
    {
      var callName = new Bpl.IdentifierExpr(f.Origin, f.FullSanitizedName + "#canCall", Bpl.Type.Bool);
      canCallFunc = new Bpl.NAryExpr(f.Origin, new Bpl.FunctionCall(callName), argsJfCanCall);
      callName = new Bpl.IdentifierExpr(overridingFunction.Origin, overridingFunction.FullSanitizedName + "#canCall", Bpl.Type.Bool);
      canCallOverridingFunc = new Bpl.NAryExpr(f.Origin, new Bpl.FunctionCall(callName), argsCfCanCall.ToList());
    }

    // useViaCanCall: C.F#canCall(args)
    Bpl.Expr useViaCanCall = canCallFunc;

    // ante := C.F#canCall(args) || (J.F#canCall(args) && $Is(this, C))
    var ante = BplOr(canCallOverridingFunc, BplAnd(canCallFunc, isOfSubtype));

    Boogie.Expr funcAppl;
    {
      var funcID = new Boogie.IdentifierExpr(f.Origin, f.FullSanitizedName, TrType(f.ResultType));
      funcAppl = new Boogie.NAryExpr(f.Origin, new Boogie.FunctionCall(funcID), argsJf);
    }
    Boogie.Expr overridingFuncAppl;
    {
      var funcID = new Boogie.IdentifierExpr(overridingFunction.Origin, overridingFunction.FullSanitizedName, TrType(overridingFunction.ResultType));
      overridingFuncAppl = new Boogie.NAryExpr(overridingFunction.Origin, new Boogie.FunctionCall(funcID), argsCf);
    }

    // Build the triggers
    // { f'(Succ(s), args') }
    Boogie.Trigger tr = BplTriggerHeap(this, overridingFunction.Origin,
      overridingFuncAppl,
      readsHeap ? etran.HeapExpr : null, isOfSubtype);
    // { f(Succ(s), args), $Is(this, T') }
    var exprs = new List<Boogie.Expr>() { funcAppl, isOfSubtype };
    if (readsHeap) {
      exprs.Add(FunctionCall(overridingFunction.Origin, BuiltinFunction.IsGoodHeap, null, etran.HeapExpr));
    }
    tr = new Boogie.Trigger(overridingFunction.Origin, true, exprs, tr);

    // The equality that is what it's all about
    var synonyms = Boogie.Expr.Eq(
      funcAppl,
      ModeledAsBoxType(f.ResultType) ? BoxIfNotNormallyBoxed(overridingFunction.Origin, overridingFuncAppl, overridingFunction.ResultType) : overridingFuncAppl);
    // add overridingFunction#canCall ==> f#canCall to the axiom
    var canCallImp = BplImp(canCallFunc, canCallOverridingFunc);

    // The axiom
    Boogie.Expr ax = BplForall(f.Origin, [], forallFormals, null, tr,
      BplImp(ante, BplAnd(canCallImp, synonyms)));
    var comment = $"override axiom for {f.FullSanitizedName} in {overridingFunction.EnclosingClass.WhatKind} {overridingFunction.EnclosingClass.FullSanitizedName}";
    return new Boogie.Axiom(f.Origin, ax, comment);
  }
}
