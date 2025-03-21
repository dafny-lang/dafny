using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using Bpl = Microsoft.Boogie;
using static Microsoft.Dafny.Util;
using PODesc = Microsoft.Dafny.ProofObligationDescription;

namespace Microsoft.Dafny {
  public partial class BoogieGenerator {
    void AddClassMembers(TopLevelDeclWithMembers c, bool includeAllMethods, bool includeInformationAboutType) {
      Contract.Requires(sink != null && Predef != null);
      Contract.Requires(c != null);
      Contract.Ensures(fuelContext == Contract.OldValue(fuelContext));
      Contract.Assert(VisibleInScope(c));

      if (includeInformationAboutType) {
        sink.AddTopLevelDeclaration(GetClass(c));
        if (c is ArrayClassDecl) {
          // classes.Add(c, predef.ClassDotArray);
          AddAllocationAxiom(null, null, (ArrayClassDecl)c, true);
        }

        if (c is ClassLikeDecl { IsReferenceTypeDecl: true } referenceTypeDecl) {
          AddIsAndIsAllocForReferenceType(referenceTypeDecl);
        }

        if (c is TraitDecl) {
          //this adds: function implements$J(Ty, typeArgs): bool;
          var arg_ref = new Bpl.Formal(c.Origin, new Bpl.TypedIdent(c.Origin, "ty", Predef.Ty), true);
          var vars = new List<Bpl.Variable> { arg_ref };
          vars.AddRange(MkTyParamFormals(GetTypeParams(c), false));
          var res = new Bpl.Formal(c.Origin, new Bpl.TypedIdent(c.Origin, Bpl.TypedIdent.NoName, Bpl.Type.Bool), false);
          var implement_intr = new Bpl.Function(c.Origin, "implements$" + c.FullSanitizedName, vars, res);
          sink.AddTopLevelDeclaration(implement_intr);
        } else if (c is ClassDecl classDecl) {
          AddImplementsAxioms(classDecl);
        }
      }

      foreach (MemberDecl member in c.Members.FindAll(VisibleInScope)) {
        Contract.Assert(IsAllocContext == null);
        CurrentDeclaration = member;
        var ignored =
          filesWhereOnlyMembersAreVerified.Contains(member.Origin.Uri) &&
          !member.HasUserAttribute("only", out _);
        if (ignored) {
          assertionOnlyFilter = _ => false;
        } else {
          SetAssertionOnlyFilter(member);
        }

        if (member is Field) {
          Field f = (Field)member;
          Boogie.Declaration fieldDeclaration;
          if (f is ConstantField) {
            // The following call has the side effect of idempotently creating and adding the function to the sink's top-level declarations
            Contract.Assert(currentModule == null);
            currentModule = f.EnclosingClass.EnclosingModuleDefinition;
            var oldFuelContext = fuelContext;
            fuelContext = FuelSetting.NewFuelContext(f);
            fieldDeclaration = GetReadonlyField(f);
            fuelContext = oldFuelContext;
            currentModule = null;
          } else {
            if (f.IsMutable) {
              fieldDeclaration = GetField(f);
              sink.AddTopLevelDeclaration(fieldDeclaration);
            } else {
              fieldDeclaration = GetReadonlyField(f);
              if (fieldDeclaration != Predef.ArrayLength) {
                sink.AddTopLevelDeclaration(fieldDeclaration);
              }
            }
          }
          AddAllocationAxiom(fieldDeclaration, f, c);
        } else if (member is Function function) {
          AddFunction_Top(function, includeAllMethods);
        } else if (member is MethodOrConstructor method) {
          AddMethod_Top(method, false, includeAllMethods);
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected member
        }
        ResetAssertionOnlyFilter();
      }
    }

    /**
      Add $Is and $IsAlloc for this class :
         axiom (forall p: ref, G: Ty ::
            { $Is(p, TClassA(G), h) }
            $Is(p, TClassA(G), h) <==> (p == null || dtype(p) == TClassA(G));
         axiom (forall p: ref, h: Heap, G: Ty ::
            { $IsAlloc(p, TClassA(G), h) }
            $IsAlloc(p, TClassA(G), h) ==> (p == null || h[p, alloc]);
     */
    private void AddIsAndIsAllocForReferenceType(ClassLikeDecl c) {
      Contract.Requires(c.IsReferenceTypeDecl);

      MapM(Bools, is_alloc => {
        var vars = MkTyParamBinders(GetTypeParams(c), out var tyexprs);

        var o = BplBoundVar("$o", Predef.RefType, vars);

        Bpl.Expr body, is_o;
        Bpl.Expr o_null = Bpl.Expr.Eq(o, Predef.Null);
        Bpl.Expr o_ty = ClassTyCon(c, tyexprs);
        string name;

        if (is_alloc) {
          name = $"$IsAlloc axiom for {c.WhatKind} {c}";
          var h = BplBoundVar("$h", Predef.HeapType, vars);
          // $IsAlloc(o, ..)
          is_o = MkIsAlloc(o, o_ty, h);
          body = BplIff(is_o, BplOr(o_null, IsAlloced(c.Origin, h, o)));
        } else {
          name = $"$Is axiom for {c.WhatKind} {c}";
          // $Is(o, ..)
          is_o = MkIs(o, o_ty);
          Bpl.Expr rhs;
          if (c == program.SystemModuleManager.ObjectDecl) {
            rhs = Bpl.Expr.True;
          } else if (c is TraitDecl) {
            //generating $o == null || implements$J(dtype(x), typeArgs)
            var t = (TraitDecl)c;
            var dtypeFunc = FunctionCall(o.tok, BuiltinFunction.DynamicType, null, o);
            var implementsJ_Arguments = new List<Expr> { dtypeFunc }; // TODO: also needs type parameters
            implementsJ_Arguments.AddRange(tyexprs);
            Bpl.Expr implementsFunc =
              FunctionCall(t.Origin, "implements$" + t.FullSanitizedName, Bpl.Type.Bool, implementsJ_Arguments);
            rhs = BplOr(o_null, implementsFunc);
          } else {
            rhs = BplOr(o_null, DType(o, o_ty));
          }

          body = BplIff(is_o, rhs);
        }

        var axiom = new Boogie.Axiom(c.Origin, BplForall(vars, BplTrigger(is_o), body), name);
        AddOtherDefinition(GetOrCreateTypeConstructor(c), axiom);
      });
    }

    void AddFunction_Top(Function f, bool includeAllMethods) {
      FuelContext oldFuelContext = this.fuelContext;
      this.fuelContext = FuelSetting.NewFuelContext(f);
      IsAllocContext = new IsAllocContext(options, true);

      AddClassMember_Function(f);

      if (InVerificationScope(f)) {
        new FunctionWellformednessChecker(this).Check(f);
        if (f.OverriddenFunction != null) { //it means that f is overriding its associated parent function
          AddFunctionOverrideCheckImpl(f);
        }
      }
      if (f is ExtremePredicate cop) {
        AddClassMember_Function(cop.PrefixPredicate);
        // skip the well-formedness check, because it has already been done for the extreme predicate
      } else if (f.ByMethodDecl != null) {
        AddMethod_Top(f.ByMethodDecl, true, includeAllMethods);
      }

      this.fuelContext = oldFuelContext;
      IsAllocContext = null;
    }

    void AddMethod_Top(MethodOrConstructor m, bool isByMethod, bool includeAllMethods) {
      if (!includeAllMethods && !InVerificationScope(m) && !referencedMembers.Contains(m)) {
        // do nothing
        return;
      }

      FuelContext oldFuelContext = this.fuelContext;
      this.fuelContext = FuelSetting.NewFuelContext(m);

      // wellformedness check for method specification
      if (m.EnclosingClass is IteratorDecl && m == ((IteratorDecl)m.EnclosingClass).Member_MoveNext) {
        // skip the well-formedness check, because it has already been done for the iterator
      } else {
        if (!isByMethod) {
          var proc = AddMethod(m, MethodTranslationKind.SpecWellformedness);
          sink.AddTopLevelDeclaration(proc);
          if (InVerificationScope(m)) {
            AddMethodImpl(m, proc, true);
          }
        }
        if (m.OverriddenMethod != null && InVerificationScope(m)) //method has overridden a parent method
        {
          var procOverrideChk = AddMethod(m, MethodTranslationKind.OverrideCheck);
          sink.AddTopLevelDeclaration(procOverrideChk);
          AddMethodOverrideCheckImpl(m, procOverrideChk);
        }
      }
      // the method spec itself
      if (!isByMethod) {
        sink.AddTopLevelDeclaration(AddMethod(m, MethodTranslationKind.Call));
      }
      if (m is ExtremeLemma) {
        // Let the CoCall and Impl forms to use m.PrefixLemma signature and specification (and
        // note that m.PrefixLemma.Body == m.Body.
        m = ((ExtremeLemma)m).PrefixLemma;
        sink.AddTopLevelDeclaration(AddMethod(m, MethodTranslationKind.CoCall));

      }
      if (!m.HasVerifyFalseAttribute && m.Body != null && InVerificationScope(m)) {
        // ...and its implementation
        assertionCount = 0;
        var proc = AddMethod(m, MethodTranslationKind.Implementation);
        sink.AddTopLevelDeclaration(proc);
        AddMethodImpl(m, proc, false);
      }
      Reset();
      this.fuelContext = oldFuelContext;
    }

    private void AddAllocationAxiom(Boogie.Declaration fieldDeclaration, Field f, TopLevelDeclWithMembers c, bool is_array = false) {
      Contract.Requires(c != null);
      // IFF you're adding the array axioms, then the field should be null
      Contract.Requires(is_array == (f == null));
      Contract.Requires(sink != null && Predef != null);

      if (f is ConstantField cf) {
        AddWellformednessCheck(cf);
      }

      if (f is ConstantField && f.IsStatic) {
        AddStaticConstFieldAllocationAxiom(fieldDeclaration, f, c);
      } else {
        AddInstanceFieldAllocationAxioms(fieldDeclaration, f, c, is_array);
      }
    }

    /// <summary>
    /// For a non-static field "f" in a class "c(G)", generate:
    ///     // type axiom:
    ///     // If "G" is empty, then TClassA(G) is omitted from trigger.
    ///     // If "c" is an array declaration, then the bound variables also include the index variables "ii" and "h[o, f]" has the form "h[o, Index(ii)]".
    ///     // If "f" is readonly, then "h[o, f]" has the form "f(o)" (for special fields) or "f(G,o)" (for programmer-declared const fields),
    ///     // so "h" and $IsHeap(h) are omitted.
    ///     axiom
    ///       (forall o: ref, h: Heap, G : Ty ::
    ///         { h[o, f], TClassA(G) }
    ///         $IsHeap(h) &&
    ///         o != null && $Is(o, TClassA(G))  // or dtype(o) = TClassA(G)
    ///         ==>
    ///         $Is(h[o, f], TT(PP)));
    ///
    ///     // allocation axiom:
    ///     // As above for "G" and "ii", but "h" is included no matter what.
    ///     axiom
    ///       (forall o: ref, h: Heap, G : Ty ::
    ///         { h[o, f], TClassA(G) }
    ///         $IsHeap(h) &&
    ///         o != null && $Is(o, TClassA(G)) &&  // or dtype(o) = TClassA(G)
    ///         h[o, alloc]
    ///         ==>
    ///         $IsAlloc(h[o, f], TT(PP), h));
    /// </summary>
    private void AddInstanceFieldAllocationAxioms(Bpl.Declaration fieldDeclaration, Field f, TopLevelDeclWithMembers c, bool is_array) {
      var bvsTypeAxiom = new List<Bpl.Variable>();
      var bvsAllocationAxiom = new List<Bpl.Variable>();

      var tyvars = MkTyParamBinders(GetTypeParams(c), out var tyexprs);
      bvsTypeAxiom.AddRange(tyvars);
      bvsAllocationAxiom.AddRange(tyvars);

      // This is the typical case (that is, f is not a static const field)

      var hVar = BplBoundVar("$h", Predef.HeapType, out var h);
      var oVar = BplBoundVar("$o", TrType(ModuleResolver.GetThisType(c.Origin, c)), out var o);

      Bpl.Expr o_ty; // to hold TClassA(G)
      var isGoodHeap = FunctionCall(c.Origin, BuiltinFunction.IsGoodHeap, null, h);
      Bpl.Expr isalloc_o;
      if (c is not ClassLikeDecl { IsReferenceTypeDecl: true }) {
        var udt = UserDefinedType.FromTopLevelDecl(c.Origin, c);
        o_ty = ClassTyCon(c, tyexprs);
        isalloc_o = MkIsAlloc(o, udt, h);
      } else if (RevealedInScope(c)) {
        o_ty = ClassTyCon(c, tyexprs);
        isalloc_o = IsAlloced(c.Origin, h, o);
      } else {
        // c is only provided, not revealed, in the scope. Use the non-null type decl's internal synonym
        var cl = (ClassLikeDecl)c;
        Contract.Assert(cl.NonNullTypeDecl != null);
        o_ty = ClassTyCon(cl.NonNullTypeDecl, tyexprs);
        var udt = UserDefinedType.FromTopLevelDecl(c.Origin, cl.NonNullTypeDecl);
        isalloc_o = MkIsAlloc(o, udt, h);
      }

      Bpl.Expr indexBounds = Bpl.Expr.True;
      Bpl.Expr oDotF;
      if (is_array) {
        // generate h[o,Index(ii)]
        bvsTypeAxiom.Add(hVar);
        bvsTypeAxiom.Add(oVar);
        bvsAllocationAxiom.Add(hVar);
        bvsAllocationAxiom.Add(oVar);

        var ac = (ArrayClassDecl)c;
        var ixs = new List<Bpl.Expr>();
        for (int i = 0; i < ac.Dims; i++) {
          Bpl.Variable v = BplBoundVar("$i" + i, Bpl.Type.Int, out var e);
          ixs.Add(e);
          bvsTypeAxiom.Add(v);
          bvsAllocationAxiom.Add(v);
        }

        oDotF = ReadHeap(c.Origin, h, o, GetArrayIndexFieldName(c.Origin, ixs));

        for (int i = 0; i < ac.Dims; i++) {
          // 0 <= i && i < _System.array.Length(o)
          var e1 = Bpl.Expr.Le(Bpl.Expr.Literal(0), ixs[i]);
          var ff = GetReadonlyField((Field)(ac.Members[i]));
          var e2 = Bpl.Expr.Lt(ixs[i], new Bpl.NAryExpr(c.Origin, new Bpl.FunctionCall(ff), new List<Bpl.Expr> { o }));
          indexBounds = BplAnd(indexBounds, BplAnd(e1, e2));
        }
      } else if (f.IsMutable) {
        // generate h[o,f]
        var ty = TrType(f.Type);
        oDotF = ReadHeap(c.Origin, h, o, new Bpl.IdentifierExpr(c.Origin, GetField(f)));
        oDotF = ty == Predef.BoxType ? oDotF : ApplyUnbox(c.Origin, oDotF, ty);
        bvsTypeAxiom.Add(hVar);
        bvsTypeAxiom.Add(oVar);
        bvsAllocationAxiom.Add(hVar);
        bvsAllocationAxiom.Add(oVar);
      } else {
        // generate f(G,o)
        var args = new List<Bpl.Expr> { o };
        if (f is ConstantField) {
          args = Concat(tyexprs, args);
        }

        oDotF = new Bpl.NAryExpr(c.Origin, new Bpl.FunctionCall(GetReadonlyField(f)), args);
        bvsTypeAxiom.Add(oVar);
        bvsAllocationAxiom.Add(hVar);
        bvsAllocationAxiom.Add(oVar);
      }

      // antecedent: some subset of: $IsHeap(h) && o != null && $Is(o, TClassA(G)) && indexBounds
      Bpl.Expr ante = Bpl.Expr.True;
      if (is_array || f.IsMutable) {
        ante = BplAnd(ante, isGoodHeap);
        // Note: for the allocation axiom, isGoodHeap is added back in for !f.IsMutable below
      }

      Bpl.Expr is_o = BplAnd(
        ReceiverNotNull(o),
        !o.Type.Equals(Predef.RefType) || c is TraitDecl
          ? MkIs(o, o_ty, ModeledAsBoxType(ModuleResolver.GetThisType(c.Origin, c))) // $Is(o, ..)
          : DType(o, o_ty)); // dtype(o) == o_ty
      ante = BplAnd(ante, is_o);

      ante = BplAnd(ante, indexBounds);

      // trigger
      var t_es = new List<Bpl.Expr>();
      t_es.Add(oDotF);
      if (tyvars.Count > 0 && (is_array || !(f is ConstantField))) {
        t_es.Add(o_ty);
      }

      var tr = new Bpl.Trigger(c.Origin, true, t_es);

      // Now for the conclusion of the axioms
      Bpl.Expr is_hf, isalloc_hf;
      if (is_array) {
        is_hf = MkIs(oDotF, tyexprs[0], true);
        isalloc_hf = MkIsAlloc(oDotF, tyexprs[0], h, true);
      } else {
        is_hf = MkIs(oDotF, f.Type); // $Is(h[o, f], ..)
        isalloc_hf = MkIsAlloc(oDotF, f.Type, h); // $IsAlloc(h[o, f], ..)
      }

      Bpl.Expr ax = BplForall(bvsTypeAxiom, tr, BplImp(ante, is_hf));
      AddOtherDefinition(fieldDeclaration, new Bpl.Axiom(c.Origin, ax, $"{c}.{f}: Type axiom"));

      if (isalloc_hf != null) {
        if (!is_array && !f.IsMutable) {
          // isGoodHeap wasn't added above, so add it now
          ante = BplAnd(isGoodHeap, ante);
        }

        ante = BplAnd(ante, isalloc_o);

        // compute a different trigger
        t_es = [
          oDotF
        ];
        if (!is_array && !f.IsMutable) {
          // since "h" is not part of oDotF, we add a separate term that mentions "h"
          t_es.Add(isalloc_o);
        }

        if (!(f is ConstantField) && tyvars.Count > 0) {
          t_es.Add(o_ty);
        }

        tr = new Bpl.Trigger(c.Origin, true, t_es);

        ax = BplForall(bvsAllocationAxiom, tr, BplImp(ante, isalloc_hf));
        AddOtherDefinition(fieldDeclaration, new Boogie.Axiom(c.Origin, ax, $"{c}.{f}: Allocation axiom"));
      }
    }

    /// <summary>
    /// For a static (necessarily "const") field "f" in a class "c(G)", the expression corresponding to "h[o, f]" or "f(G,o)" above is "f(G)",
    /// so generate:
    ///     // type axiom:
    ///     axiom
    ///       (forall G : Ty ::
    ///         { f(G) }
    ///         $Is(f(G), TT(PP)));
    ///     // Or in the case where G is empty:
    ///     axiom $Is(f(G), TT);
    ///
    ///     // allocation axiom:
    ///     axiom
    ///       (forall h: Heap, G : Ty ::
    ///         { $IsAlloc(f(G), TT(PP), h) }
    ///         $IsHeap(h)
    ///       ==>
    ///         $IsAlloc(f(G), TT(PP), h));
    ///
    ///
    /// The axioms above could be optimised to something along the lines of:
    ///     axiom
    ///       (forall o: ref, h: Heap ::
    ///         { h[o, f] }
    ///         $IsHeap(h) && o != null && Tag(dtype(o)) = TagClass
    ///         ==>
    ///         (h[o, alloc] ==> $IsAlloc(h[o, f], TT(TClassA_Inv_i(dtype(o)),..), h)) &&
    ///         $Is(h[o, f], TT(TClassA_Inv_i(dtype(o)),..), h);
    /// </summary>
    private void AddStaticConstFieldAllocationAxiom(Boogie.Declaration fieldDeclaration, Field f, TopLevelDeclWithMembers c) {

      var bvsTypeAxiom = new List<Bpl.Variable>();
      var bvsAllocationAxiom = new List<Bpl.Variable>();

      var tyvars = MkTyParamBinders(GetTypeParams(c), out var tyexprs);
      bvsTypeAxiom.AddRange(tyvars);
      bvsAllocationAxiom.AddRange(tyvars);

      var oDotF = new Boogie.NAryExpr(c.Origin, new Boogie.FunctionCall(GetReadonlyField(f)), tyexprs);
      var is_hf = MkIs(oDotF, f.Type); // $Is(h[o, f], ..)
      Boogie.Expr ax = bvsTypeAxiom.Count == 0 ? is_hf : BplForall(bvsTypeAxiom, BplTrigger(oDotF), is_hf);
      var isAxiom = new Boogie.Axiom(c.Origin, ax, $"{c}.{f}: Type axiom");
      AddOtherDefinition(fieldDeclaration, isAxiom);

      {
        var hVar = BplBoundVar("$h", Predef.HeapType, out var h);
        bvsAllocationAxiom.Add(hVar);
        var isGoodHeap = FunctionCall(c.Origin, BuiltinFunction.IsGoodHeap, null, h);
        var isalloc_hf = MkIsAlloc(oDotF, f.Type, h); // $IsAlloc(h[o, f], ..)
        ax = BplForall(bvsAllocationAxiom, BplTrigger(isalloc_hf), BplImp(isGoodHeap, isalloc_hf));
        var isAllocAxiom = new Boogie.Axiom(c.Origin, ax, $"{c}.{f}: Allocation axiom");
        sink.AddTopLevelDeclaration(isAllocAxiom);
      }
    }

    private void AddImplementsAxioms(ClassDecl c) {
      //this adds: axiom implements$J(class.C, typeInstantiations);
      var vars = MkTyParamBinders(GetTypeParams(c), out var tyexprs);

      foreach (var parent in c.Traits) {
        var trait = ((UserDefinedType)parent).AsParentTraitDecl();
        Contract.Assert(trait != null);
        var arg = ClassTyCon(c, tyexprs);
        var args = new List<Bpl.Expr> { arg };
        foreach (var targ in parent.TypeArgs) {
          args.Add(TypeToTy(targ));
        }
        var expr = FunctionCall(c.Origin, "implements$" + trait.FullSanitizedName, Bpl.Type.Bool, args);
        var implements_axiom = new Bpl.Axiom(c.Origin, BplForall(vars, null, expr));
        AddOtherDefinition(GetOrCreateTypeConstructor(c), implements_axiom);
      }
    }

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

    private void AddMethodImpl(MethodOrConstructor m, Bpl.Procedure proc, bool wellformednessProc) {
      Contract.Requires(m != null);
      Contract.Requires(proc != null);
      Contract.Requires(sink != null && Predef != null);
      Contract.Requires(wellformednessProc || m.Body != null);
      Contract.Requires(currentModule == null && codeContext == null && _tmpIEs.Count == 0 && IsAllocContext == null);
      Contract.Ensures(currentModule == null && codeContext == null && _tmpIEs.Count == 0 && IsAllocContext == null);

      proofDependencies.SetCurrentDefinition(proc.VerboseName, m);
      currentModule = m.EnclosingClass.EnclosingModuleDefinition;
      codeContext = m;
      IsAllocContext = new IsAllocContext(options, m.IsGhost);

      List<Variable> inParams = Boogie.Formal.StripWhereClauses(proc.InParams);
      List<Variable> outParams = Boogie.Formal.StripWhereClauses(proc.OutParams);

      var builder = new BoogieStmtListBuilder(this, options, new BodyTranslationContext(m.ContainsHide));
      builder.Add(new CommentCmd("AddMethodImpl: " + m + ", " + proc));
      var etran = new ExpressionTranslator(this, Predef, m.Origin,
        m is Method { IsByMethod: true } ? m.FunctionFromWhichThisIsByMethodDecl : m);
      // Only do reads checks for methods, not lemmas
      // (which aren't allowed to declare frames and don't check reads and writes against them).
      // Also don't do any reads checks if the reads clause is *,
      // since all the checks will be trivially true
      // and we don't need to cause additional verification cost for existing code.
      if (!options.Get(MethodOrConstructor.ReadsClausesOnMethods) || m.IsLemmaLike || m.Reads.Expressions.Exists(e => e.E is WildcardExpr)) {
        etran = etran.WithReadsFrame(null);
      }
      InitializeFuelConstant(m.Origin, builder, etran);
      var localVariables = new Variables();
      GenerateImplPrelude(m, wellformednessProc, inParams, outParams, builder, localVariables, etran);

      if (UseOptimizationInZ3) {
        // We ask Z3 to minimize all parameters of type 'nat'.
        foreach (var f in m.Ins) {
          if (f.Type.NormalizeExpandKeepConstraints() is UserDefinedType udt && udt.Name == "nat") {
            builder.Add(optimizeExpr(true, new IdentifierExpr(f.Origin, f), f.Origin, etran));
          }
        }
      }

      var stmts = wellformednessProc
        ? TrMethodContractWellformednessCheck(m, etran, localVariables, builder, outParams)
        : TrMethodBody(m, builder, localVariables, etran);

      if (EmitImplementation(m.Attributes)) {
        // emit impl only when there are proof obligations.
        QKeyValue kv = etran.TrAttributes(m.Attributes, null);
        var impl = AddImplementationWithAttributes(GetToken(m), proc,
           inParams, outParams, localVariables, stmts, kv);

        if (InsertChecksums) {
          InsertChecksum(m, impl);
        }
      }

      IsAllocContext = null;
      Reset();
    }

    private StmtList TrMethodContractWellformednessCheck(MethodOrConstructor m, ExpressionTranslator etran, Variables localVariables,
      BoogieStmtListBuilder builder, List<Variable> outParams) {
      var builderInitializationArea = new BoogieStmtListBuilder(this, options, builder.Context);
      StmtList stmts;
      var readsCheckDelayer = new ReadsCheckDelayer(etran, null, localVariables, builderInitializationArea, builder);

      // check well-formedness of any default-value expressions (before assuming preconditions)
      readsCheckDelayer.DoWithDelayedReadsChecks(true, wfo => {
        foreach (var formal in m.Ins.Where(formal => formal.DefaultValue != null)) {
          var e = formal.DefaultValue;
          CheckWellformed(e, wfo, localVariables, builder, etran.WithReadsFrame(etran.readsFrame, null)); // No scope for default parameters
          builder.Add(new Boogie.AssumeCmd(e.Origin, etran.CanCallAssumption(e)));
          CheckSubrange(e.Origin, etran.TrExpr(e), e.Type, formal.Type, e, builder);

          if (formal.IsOld) {
            Boogie.Expr wh = GetWhereClause(e.Origin, etran.TrExpr(e), e.Type, etran.Old, ISALLOC, true);
            if (wh != null) {
              var desc = new IsAllocated("default value", "in the two-state lemma's previous state", e);
              builder.Add(Assert(e.Origin, wh, desc, builder.Context));
            }
          }
        }
      });

      // check well-formedness of the preconditions, and then assume each one of them
      readsCheckDelayer.DoWithDelayedReadsChecks(false, wfo => {
        foreach (AttributedExpression p in ConjunctsOf(m.Req)) {
          CheckWellformedAndAssume(p.E, wfo, localVariables, builder, etran, "method requires clause");
        }
      });

      // check well-formedness of the reads clauses
      readsCheckDelayer.DoWithDelayedReadsChecks(false, wfo => {
        CheckFrameWellFormed(wfo, m.Reads.Expressions, localVariables, builder, etran);
      });
      // Also check that the reads clause == {} if the {:concurrent} attribute is present
      // on the method, and {:assume_concurrent} is NOT present on the reads clause.
      if (Attributes.Contains(m.Attributes, Attributes.ConcurrentAttributeName) &&
          !Attributes.Contains(m.Reads.Attributes, Attributes.AssumeConcurrentAttributeName)) {
        var desc = new ConcurrentFrameEmpty(m, "reads");
        if (etran.readsFrame != null) {
          CheckFrameEmpty(m.Origin, etran, etran.ReadsFrame(m.Origin), builder, desc, null);
        } else {
          // etran.readsFrame being null indicates the default of reads *,
          // so this is an automatic failure.
          builder.Add(Assert(m.Origin, Expr.False, desc, builder.Context));
        }
      }

      // check well-formedness of the modifies clauses
      readsCheckDelayer.DoWithDelayedReadsChecks(false, wfo => {
        CheckFrameWellFormed(wfo, m.Mod.Expressions, localVariables, builder, etran);
      });
      // Also check that the modifies clause == {} if the {:concurrent} attribute is present,
      // and {:assume_concurrent} is NOT present on the modifies clause.
      if (Attributes.Contains(m.Attributes, Attributes.ConcurrentAttributeName) &&
          !Attributes.Contains(m.Mod.Attributes, Attributes.AssumeConcurrentAttributeName)) {
        var desc = new ConcurrentFrameEmpty(m, "modifies");
        CheckFrameEmpty(m.Origin, etran, etran.ModifiesFrame(m.Origin), builder, desc, null);
      }

      // check well-formedness of the decreases clauses
      var wfOptions = new WFOptions();
      foreach (Expression p in m.Decreases.Expressions) {
        CheckWellformed(p, wfOptions, localVariables, builder, etran);
      }

      if (m is not TwoStateLemma) {
        var modifies = m.Mod;
        var allowsAllocation = m.AllowsAllocation;

        ApplyModifiesEffect(m, etran, builder, modifies, allowsAllocation, m.IsGhost);
      }

      // also play havoc with the out parameters
      if (outParams.Count != 0) {  // don't create an empty havoc statement
        List<Boogie.IdentifierExpr> outH = [];
        foreach (Boogie.Variable b in outParams) {
          Contract.Assert(b != null);
          outH.Add(new Boogie.IdentifierExpr(b.tok, b));
        }
        builder.Add(new Boogie.HavocCmd(m.Origin, outH));
        if (m is Constructor) {
          var receiverType = ModuleResolver.GetReceiverType(m.Origin, m);
          var receiver = new Bpl.IdentifierExpr(m.Origin, "this", TrType(receiverType));
          var wh = BplAnd(
            ReceiverNotNull(receiver),
            GetWhereClause(m.Origin, receiver, receiverType, etran, IsAllocType.ISALLOC));
          builder.Add(TrAssumeCmd(m.Origin, wh));
        }
      }
      // mark the end of the modifies/out-parameter havocking with a CaptureState; make its location be the first ensures clause, if any (and just
      // omit the CaptureState if there's no ensures clause)
      if (m.Ens.Count != 0) {
        builder.AddCaptureState(m.Ens[0].E.Origin, false, "post-state");
      }

      // check wellformedness of postconditions
      foreach (AttributedExpression p in ConjunctsOf(m.Ens)) {
        CheckWellformedAndAssume(p.E, wfOptions, localVariables, builder, etran, "method ensures clause");
      }

      var s0 = builderInitializationArea.Collect(m.Origin);
      var s1 = builder.Collect(m.Origin);
      stmts = new StmtList(new List<BigBlock>(s0.BigBlocks.Concat(s1.BigBlocks)), m.Origin);
      return stmts;
    }

    public void ApplyModifiesEffect(INode node, ExpressionTranslator etran, BoogieStmtListBuilder builder,
      Specification<FrameExpression> modifies, bool allowsAllocation, bool isGhostContext) {
      // play havoc with the heap according to the modifies clause
      builder.Add(new Boogie.HavocCmd(node.Origin, [etran.HeapCastToIdentifierExpr]));
      // assume the usual two-state boilerplate information
      foreach (BoilerplateTriple tri in GetTwoStateBoilerplate(node.Origin, modifies.Expressions, isGhostContext, allowsAllocation, etran.Old, etran, etran.Old)) {
        if (tri.IsFree) {
          builder.Add(TrAssumeCmd(node.Origin, tri.Expr));
        }
      }
    }

    private StmtList TrMethodBody(MethodOrConstructor m, BoogieStmtListBuilder builder, Variables localVariables,
      ExpressionTranslator etran) {
      var inductionVars = ApplyInduction(m.Ins, m.Attributes);
      if (inductionVars.Count != 0) {
        // Let the parameters be this,x,y of the method M and suppose ApplyInduction returns this,y.
        // Also, let Pre be the precondition and VF be the decreases clause.
        // Then, insert into the method body what amounts to:
        //     assume case-analysis-on-parameter[[ y' ]];
        //     forall this',y' | Pre(this', x, y') && (VF(this', x, y') << VF(this', x, y)) {
        //       this'.M(x, y');
        //     }
        // Generate bound variables for the forall statement, and a substitution for the Pre and VF

        // assume case-analysis-on-parameter[[ y' ]];
        foreach (var inFormal in m.Ins) {
          var dt = inFormal.Type.AsDatatype;
          if (dt != null) {
            var funcID = new Boogie.FunctionCall(new Boogie.IdentifierExpr(inFormal.Origin, "$IsA#" + dt.FullSanitizedName, Boogie.Type.Bool));
            var f = new Boogie.IdentifierExpr(inFormal.Origin, inFormal.AssignUniqueName(m.IdGenerator), TrType(inFormal.Type));
            builder.Add(TrAssumeCmd(inFormal.Origin, new Boogie.NAryExpr(inFormal.Origin, funcID, new List<Boogie.Expr> { f })));
          }
        }

        var parBoundVars = new List<BoundVar>();
        var parBounds = new List<BoundedPool>();
        var substMap = new Dictionary<IVariable, Expression>();
        Expression receiverSubst = null;
        foreach (var iv in inductionVars) {
          BoundVar bv;
          if (iv == null) {
            // this corresponds to "this"
            Contract.Assert(!m.IsStatic);  // if "m" is static, "this" should never have gone into the _induction attribute
            Contract.Assert(receiverSubst == null);  // we expect at most one
            var receiverType = ModuleResolver.GetThisType(m.Origin, (TopLevelDeclWithMembers)m.EnclosingClass);
            bv = new BoundVar(m.Origin, CurrentIdGenerator.FreshId("$ih#this"), receiverType); // use this temporary variable counter, but for a Dafny name (the idea being that the number and the initial "_" in the name might avoid name conflicts)
            var ie = new IdentifierExpr(m.Origin, bv.Name) {
              Var = bv,
              Type = bv.Type
            };
            receiverSubst = ie;
          } else {
            CloneVariableAsBoundVar(iv.Origin, iv, "$ih#" + iv.Name, out bv, out var ie);
            substMap.Add(iv, ie);
          }
          parBoundVars.Add(bv);
          parBounds.Add(new SpecialAllocIndependenceAllocatedBoundedPool());  // record that we don't want alloc antecedents for these variables
        }

        // Generate a CallStmt to be used as the body of the 'forall' statement.
        m.RecursiveCallParameters(m.Origin, m.TypeArgs, m.Ins, receiverSubst, substMap, out var recursiveCallReceiver, out var recursiveCallArgs);
        var methodSel = new MemberSelectExpr(m.Origin, recursiveCallReceiver, m.NameNode) {
          Member = m,
          TypeApplicationAtEnclosingClass = m.EnclosingClass.TypeArgs.ConvertAll(tp => (Type)new UserDefinedType(tp.Origin, tp)),
          TypeApplicationJustMember = m.TypeArgs.ConvertAll(tp => (Type)new UserDefinedType(tp.Origin, tp)),
          Type = new InferredTypeProxy()
        };
        var recursiveCall = new CallStmt(m.Origin, [], methodSel, recursiveCallArgs) {
          IsGhost = m.IsGhost
        };

        Expression parRange = Expression.CreateBoolLiteral(m.Origin, true);
        foreach (var pre in m.Req) {
          parRange = Expression.CreateAnd(parRange, Substitute(pre.E, receiverSubst, substMap));
        }

        // construct an expression (generator) for:  VF' << VF
        ExpressionConverter decrCheck = delegate (Dictionary<IVariable, Expression> decrSubstMap, ExpressionTranslator exprTran) {
          var decrToks = new List<IOrigin>();
          var decrTypes = new List<Type>();
          var decrCallee = new List<Expr>();
          var decrCaller = new List<Expr>();
          var decrCalleeDafny = new List<Expression>();
          var decrCallerDafny = new List<Expression>();
          Bpl.Expr canCalls = Bpl.Expr.True;
          foreach (var ee in m.Decreases.Expressions) {
            decrToks.Add(ee.Origin);
            decrTypes.Add(ee.Type.NormalizeExpand());
            decrCallerDafny.Add(ee);
            canCalls = BplAnd(canCalls, exprTran.CanCallAssumption(ee));
            decrCaller.Add(exprTran.TrExpr(ee));
            Expression es = Substitute(ee, receiverSubst, substMap);
            es = Substitute(es, null, decrSubstMap);
            decrCalleeDafny.Add(es);
            canCalls = BplAnd(canCalls, exprTran.CanCallAssumption(ee));
            decrCallee.Add(exprTran.TrExpr(es));
          }
          return BplImp(canCalls,
            DecreasesCheck(decrToks, null, decrCalleeDafny, decrCallerDafny, decrCallee, decrCaller, null, null, false, true));
        };

        var triggers = m.Attributes.AsEnumerable()
          .Where(attr => attr.Name is "inductionTrigger" or "_inductionTrigger")
          .Select(attr => attr.Args)
          .ToList();
#if VERIFY_CORRECTNESS_OF_TRANSLATION_FORALL_STATEMENT_RANGE
        var definedness = new BoogieStmtListBuilder(this, options, builder.Context);
        var exporter = new BoogieStmtListBuilder(this, options, builder.Context);
        TrForallStmtCall(m.Origin, parBoundVars, parBounds, parRange, decrCheck, null, triggers, recursiveCall, definedness,
          exporter, localVariables, etran);
        // All done, so put the two pieces together
        builder.Add(new Bpl.IfCmd(m.Origin, null, definedness.Collect(m.Origin), null, exporter.Collect(m.Origin)));
#else
        TrForallStmtCall(m.Origin, parBoundVars, parBounds, parRange, decrCheck, null, triggers, recursiveCall, null,
          builder, localVariables, etran, includeCanCalls: true);
#endif
      }
      // translate the body of the method
      Contract.Assert(m.Body != null);  // follows from method precondition and the if guard

      // $_reverifyPost := false;
      builder.Add(Boogie.Cmd.SimpleAssign(m.Origin, new Boogie.IdentifierExpr(m.Origin, "$_reverifyPost", Boogie.Type.Bool), Boogie.Expr.False));
      // register output parameters with definite-assignment trackers

      var beforeOutTrackers = DefiniteAssignmentTrackers;
      m.Outs.ForEach(p => AddExistingDefiniteAssignmentTracker(p, m.IsGhost));
      // translate the body
      TrStmt(m.Body, builder, localVariables, etran);
      m.Outs.ForEach(p => CheckDefiniteAssignmentReturn(m.Body.EndToken, p, builder));
      if (m is { FunctionFromWhichThisIsByMethodDecl: { ByMethodTok: { } } fun }) {
        AssumeCanCallForByMethodDecl(m, builder);
      }
      var stmts = builder.Collect(m.Body.StartToken); // EndToken might make more sense, but it requires updating most of the regression tests.
      DefiniteAssignmentTrackers = beforeOutTrackers;
      return stmts;
    }

    private void AddMethodOverrideCheckImpl(MethodOrConstructor m, Boogie.Procedure proc) {
      Contract.Requires(m != null);
      Contract.Requires(proc != null);
      Contract.Requires(sink != null && Predef != null);
      Contract.Requires(m.OverriddenMethod != null);
      Contract.Requires(m.Ins.Count == m.OverriddenMethod.Ins.Count);
      Contract.Requires(m.Outs.Count == m.OverriddenMethod.Outs.Count);
      //Contract.Requires(wellformednessProc || m.Body != null);
      Contract.Requires(currentModule == null && codeContext == null && _tmpIEs.Count == 0 && IsAllocContext == null);
      Contract.Ensures(currentModule == null && codeContext == null && _tmpIEs.Count == 0 && IsAllocContext == null);

      proofDependencies.SetCurrentDefinition(proc.VerboseName, m);
      currentModule = m.EnclosingClass.EnclosingModuleDefinition;
      codeContext = m;
      IsAllocContext = new IsAllocContext(options, m.IsGhost);

      List<Variable> inParams = Boogie.Formal.StripWhereClauses(proc.InParams);
      List<Variable> outParams = Boogie.Formal.StripWhereClauses(proc.OutParams);

      var builder = new BoogieStmtListBuilder(this, options, new BodyTranslationContext(false));
      var etran = new ExpressionTranslator(this, Predef, m.Origin, m);
      var localVariables = new Variables();
      InitializeFuelConstant(m.Origin, builder, etran);

      // assume traitTypeParameter == G(overrideTypeParameters);
      AddOverrideCheckTypeArgumentInstantiations(m, builder, localVariables);

      if (m is TwoStateLemma) {
        // $Heap := current$Heap;
        var heap = ExpressionTranslator.HeapIdentifierExpr(Predef, m.Origin);
        builder.Add(Boogie.Cmd.SimpleAssign(m.Origin, heap, new Boogie.IdentifierExpr(m.Origin, "current$Heap", Predef.HeapType)));
      }


      var substMap = new Dictionary<IVariable, Expression>();
      for (int i = 0; i < m.Ins.Count; i++) {
        // get corresponding formal in the class
        var ie = new IdentifierExpr(m.Ins[i].Origin, m.Ins[i].AssignUniqueName(m.IdGenerator));
        ie.Var = m.Ins[i]; ie.Type = ie.Var.Type;
        substMap.Add(m.OverriddenMethod.Ins[i], ie);
      }
      for (int i = 0; i < m.Outs.Count; i++) {
        // get corresponding formal in the class
        var ie = new IdentifierExpr(m.Outs[i].Origin, m.Outs[i].AssignUniqueName(m.IdGenerator));
        ie.Var = m.Outs[i]; ie.Type = ie.Var.Type;
        substMap.Add(m.OverriddenMethod.Outs[i], ie);
      }

      var typeMap = GetTypeArgumentSubstitutionMap(m.OverriddenMethod, m);

      Boogie.StmtList stmts;
      //adding assume Pre’; assert P; // this checks that Pre’ implies P
      AddMethodOverrideReqsChk(m, builder, etran, substMap, typeMap);

      //adding assert R <= Rank’;
      AddOverrideTerminationChk(m, m.OverriddenMethod, builder, etran, substMap, typeMap);

      //adding assert F <= Frame’ (for both reads and modifies clauses)
      AddMethodOverrideFrameSubsetChk(m, false, builder, etran, localVariables, substMap, typeMap);
      AddMethodOverrideFrameSubsetChk(m, true, builder, etran, localVariables, substMap, typeMap);

      if (!(m is TwoStateLemma)) {
        //change the heap at locations W
        HavocMethodFrameLocations(m, builder, etran, localVariables);
      }

      //adding assume Q; assert Post’;
      AddMethodOverrideEnsChk(m, builder, etran, substMap, typeMap);

      stmts = builder.Collect(m.Origin);

      if (EmitImplementation(m.Attributes)) {
        // emit the impl only when there are proof obligations.
        QKeyValue kv = etran.TrAttributes(m.Attributes, null);

        Boogie.Implementation impl = AddImplementationWithAttributes(GetToken(m), proc, inParams, outParams, localVariables, stmts, kv);

        if (InsertChecksums) {
          InsertChecksum(m, impl);
        }
      }

      IsAllocContext = null;
      Reset();
    }

    private void HavocMethodFrameLocations(MethodOrConstructor m, BoogieStmtListBuilder builder, ExpressionTranslator etran, Variables localVariables) {
      Contract.Requires(m != null);
      Contract.Requires(m.EnclosingClass != null && m.EnclosingClass is ClassLikeDecl);

      // play havoc with the heap according to the modifies clause
      builder.Add(new Bpl.HavocCmd(m.Origin, [etran.HeapCastToIdentifierExpr]));
      // assume the usual two-state boilerplate information
      foreach (BoilerplateTriple tri in GetTwoStateBoilerplate(m.Origin, m.Mod.Expressions, m.IsGhost, m.AllowsAllocation, etran.Old, etran, etran.Old)) {
        if (tri.IsFree) {
          builder.Add(TrAssumeCmd(m.Origin, tri.Expr));
        }
      }
    }

    private void AddFunctionOverrideCheckImpl(Function f) {
      Contract.Requires(f != null);
      Contract.Requires(f.EnclosingClass is TopLevelDeclWithMembers);
      Contract.Requires(sink != null && Predef != null);
      Contract.Requires(f.OverriddenFunction != null);
      Contract.Requires(f.Ins.Count == f.OverriddenFunction.Ins.Count);
      Contract.Requires(currentModule == null && codeContext == null && _tmpIEs.Count == 0 && IsAllocContext != null);
      Contract.Ensures(currentModule == null && codeContext == null && _tmpIEs.Count == 0 && IsAllocContext != null);

      proofDependencies.SetCurrentDefinition(MethodVerboseName(f.FullDafnyName, MethodTranslationKind.OverrideCheck), f);
      #region first procedure, no impl yet
      //Function nf = new Function(f.Tok, "OverrideCheck_" + f.Name, f.IsStatic, f.IsGhost, f.TypeArgs, f.OpenParen, f.Formals, f.ResultType, f.Req, f.Reads, f.Ens, f.Decreases, f.Body, f.Attributes, f.SignatureEllipsis);
      //AddFunction(f);
      currentModule = f.EnclosingClass.EnclosingModuleDefinition;
      codeContext = f;

      Boogie.Expr prevHeap = null;
      Boogie.Expr currHeap = null;
      var ordinaryEtran = new ExpressionTranslator(this, Predef, f.Origin, f);
      ExpressionTranslator etran;
      var inParams_Heap = new List<Boogie.Variable>();
      if (f is TwoStateFunction) {
        var prevHeapVar = new Boogie.Formal(f.Origin, new Boogie.TypedIdent(f.Origin, "previous$Heap", Predef.HeapType), true);
        inParams_Heap.Add(prevHeapVar);
        prevHeap = new Boogie.IdentifierExpr(f.Origin, prevHeapVar);
        if (f.ReadsHeap) {
          var currHeapVar = new Boogie.Formal(f.Origin, new Boogie.TypedIdent(f.Origin, "current$Heap", Predef.HeapType), true);
          inParams_Heap.Add(currHeapVar);
          currHeap = new Boogie.IdentifierExpr(f.Origin, currHeapVar);
        }
        etran = new ExpressionTranslator(this, Predef, currHeap, prevHeap, f);
      } else {
        etran = ordinaryEtran;
      }

      // parameters of the procedure
      var typeInParams = MkTyParamFormals(GetTypeParams(f), true);
      var inParams = new List<Variable>();
      var outParams = new List<Boogie.Variable>();
      if (!f.IsStatic) {
        var th = new Boogie.IdentifierExpr(f.Origin, "this", TrReceiverType(f));
        Boogie.Expr wh = BplAnd(
          ReceiverNotNull(th),
          etran.GoodRef(f.Origin, th, ModuleResolver.GetReceiverType(f.Origin, f)));
        Boogie.Formal thVar = new Boogie.Formal(f.Origin, new Boogie.TypedIdent(f.Origin, "this", TrReceiverType(f), wh), true);
        inParams.Add(thVar);
      }
      foreach (Formal p in f.Ins) {
        Boogie.Type varType = TrType(p.Type);
        Boogie.Expr wh = GetWhereClause(p.Origin, new Boogie.IdentifierExpr(p.Origin, p.AssignUniqueName(f.IdGenerator), varType), p.Type, etran, NOALLOC);
        inParams.Add(new Boogie.Formal(p.Origin, new Boogie.TypedIdent(p.Origin, p.AssignUniqueName(f.IdGenerator), varType, wh), true));
      }

      Formal pOut = null;
      if (f.Result != null || f.OverriddenFunction.Result != null) {
        if (f.Result != null) {
          pOut = f.Result;
          Contract.Assert(!pOut.IsOld);
        } else {
          var pp = f.OverriddenFunction.Result;
          Contract.Assert(!pp.IsOld);
          pOut = new Formal(pp.Origin, pp.NameNode, f.ResultType, false, pp.IsGhost, null);
        }
        var varType = TrType(pOut.Type);
        var wh = GetWhereClause(pOut.Origin, new Boogie.IdentifierExpr(pOut.Origin, pOut.AssignUniqueName(f.IdGenerator), varType), pOut.Type, etran, NOALLOC);
        outParams.Add(new Boogie.Formal(pOut.Origin, new Boogie.TypedIdent(pOut.Origin, pOut.AssignUniqueName(f.IdGenerator), varType, wh), true));
      }
      // the procedure itself
      var req = new List<Boogie.Requires>();
      if (f is TwoStateFunction) {
        // free requires prevHeap == Heap && HeapSucc(prevHeap, currHeap) && IsHeap(currHeap)
        var a0 = Boogie.Expr.Eq(prevHeap, ordinaryEtran.HeapExpr);
        var a1 = HeapSucc(prevHeap, currHeap);
        var a2 = FunctionCall(f.Origin, BuiltinFunction.IsGoodHeap, null, currHeap);
        req.Add(FreeRequires(f.Origin, BplAnd(a0, BplAnd(a1, a2)), null));
      }
      foreach (var typeBoundAxiom in TypeBoundAxioms(f.Origin, Concat(f.EnclosingClass.TypeArgs, f.TypeArgs))) {
        req.Add(Requires(f.Origin, true, null, typeBoundAxiom, null, null, null));
      }

      // modifies $Heap
      var mod = new List<Boogie.IdentifierExpr> {
        ordinaryEtran.HeapCastToIdentifierExpr,
      };
      var ens = new List<Boogie.Ensures>();

      var name = MethodName(f, MethodTranslationKind.OverrideCheck);
      var implicitParameters = Util.Concat(typeInParams, inParams_Heap);
      var proc = new Boogie.Procedure(f.Origin, name, [],
        Util.Concat(implicitParameters, inParams), outParams,
        false, req, mod, ens, etran.TrAttributes(f.Attributes, null));
      AddVerboseNameAttribute(proc, f.FullDafnyName, MethodTranslationKind.OverrideCheck);
      sink.AddTopLevelDeclaration(proc);
      var implImplicitParams = Boogie.Formal.StripWhereClauses(implicitParameters);
      var implInParams = Boogie.Formal.StripWhereClauses(inParams);
      var implOutParams = Boogie.Formal.StripWhereClauses(outParams);

      #endregion

      BoogieStmtListBuilder builder = new BoogieStmtListBuilder(this, options, new BodyTranslationContext(false));
      var localVariables = new Variables();

      InitializeFuelConstant(f.Origin, builder, etran);

      // assume traitTypeParameter == G(overrideTypeParameters);
      AddOverrideCheckTypeArgumentInstantiations(f, builder, localVariables);

      if (f is TwoStateFunction) {
        // $Heap := current$Heap;
        var heap = ordinaryEtran.HeapCastToIdentifierExpr;
        builder.Add(Boogie.Cmd.SimpleAssign(f.Origin, heap, etran.HeapExpr));
        etran = ordinaryEtran;  // we no longer need the special heap names
      }

      var substMap = new Dictionary<IVariable, Expression>();
      foreach (var (formal, overriddenFormal) in f.Ins.Zip(f.OverriddenFunction.Ins, Tuple.Create)) {
        // get corresponding formal in the class
        var ie = new IdentifierExpr(formal.Origin, formal.AssignUniqueName(f.IdGenerator)) { Var = formal, Type = formal.Type };
        substMap.Add(overriddenFormal, ie);
      }

      if (f.OverriddenFunction.Result != null) {
        Contract.Assert(pOut != null);
        //get corresponding formal in the class
        var ie = new IdentifierExpr(pOut.Origin, pOut.AssignUniqueName(f.IdGenerator)) { Var = pOut, Type = pOut.Type };
        substMap.Add(f.OverriddenFunction.Result, ie);
      }

      var typeMap = GetTypeArgumentSubstitutionMap(f.OverriddenFunction, f);

      //adding assume Pre’; assert P; // this checks that Pre’ implies P
      AddFunctionOverrideReqsChk(f, builder, etran, substMap, typeMap);

      //adding assert R <= Rank’;
      AddOverrideTerminationChk(f, f.OverriddenFunction, builder, etran, substMap, typeMap);

      //adding assert W <= Frame’
      AddFunctionOverrideSubsetChk(f, builder, etran, localVariables, substMap, typeMap);

      //adding assume Q; assert Post’;
      AddFunctionOverrideEnsChk(f, builder, etran, substMap, typeMap, implInParams, implOutParams.Count == 0 ? null : implOutParams[0]);

      var stmts = builder.Collect(f.Origin);

      if (EmitImplementation(f.Attributes)) {
        // emit the impl only when there are proof obligations.
        QKeyValue kv = etran.TrAttributes(f.Attributes, null);

        AddImplementationWithAttributes(GetToken(f), proc,
            Util.Concat(implImplicitParams, implInParams),
            implOutParams, localVariables, stmts, kv);
      }

      if (InsertChecksums) {
        InsertChecksum(f, proc, true);
      }

      Reset();
    }


    private void AddFunctionOverrideEnsChk(Function f, BoogieStmtListBuilder builder, ExpressionTranslator etran,
      Dictionary<IVariable, Expression> substMap, Dictionary<TypeParameter, Type> typeMap,
      List<Bpl.Variable> implInParams, Bpl.Variable/*?*/ resultVariable) {
      Contract.Requires(f.Ins.Count <= implInParams.Count);

      var cco = new CanCallOptions(true, f);
      //generating class post-conditions
      foreach (var en in ConjunctsOf(f.Ens)) {
        builder.Add(TrAssumeCmd(f.Origin, etran.CanCallAssumption(en.E, cco)));
        builder.Add(TrAssumeCmdWithDependencies(etran, f.Origin, en.E, "overridden function ensures clause"));
      }

      //generating assume C.F(ins) == out, if a result variable was given
      if (resultVariable != null) {
        var funcIdC = new FunctionCall(new Bpl.IdentifierExpr(f.Origin, f.FullSanitizedName, TrType(f.ResultType)));
        var argsC = new List<Bpl.Expr>();

        // add type arguments
        argsC.AddRange(GetTypeArguments(f, null).ConvertAll(TypeToTy));

        // add fuel arguments
        if (f.IsFuelAware()) {
          argsC.Add(etran.layerInterCluster.GetFunctionFuel(f));
        }

        if (f.IsOpaque || f.IsMadeImplicitlyOpaque(options)) {
          argsC.Add(GetRevealConstant(f));
        }

        // add heap arguments
        if (f is TwoStateFunction) {
          argsC.Add(etran.Old.HeapExpr);
        }
        if (f.ReadsHeap) {
          argsC.Add(etran.HeapExpr);
        }

        argsC.AddRange(implInParams.Select(var => new Bpl.IdentifierExpr(f.Origin, var)));

        var funcExpC = new Bpl.NAryExpr(f.Origin, funcIdC, argsC);
        var resultVar = new Bpl.IdentifierExpr(resultVariable.tok, resultVariable);
        builder.Add(TrAssumeCmd(f.Origin, Bpl.Expr.Eq(funcExpC, resultVar)));
      }

      // conjunction of class post-conditions
      var allOverrideEns = f.Ens
        .Select(e => e.E)
        .Aggregate((Expression)Expression.CreateBoolLiteral(f.Origin, true), (e0, e1) => Expression.CreateAnd(e0, e1));
      //generating trait post-conditions with class variables
      cco = new CanCallOptions(true, f, true);
      FunctionCallSubstituter sub = new FunctionCallSubstituter(substMap, typeMap,
        (TraitDecl)f.OverriddenFunction.EnclosingClass, (TopLevelDeclWithMembers)f.EnclosingClass);
      foreach (var en in ConjunctsOf(f.OverriddenFunction.Ens)) {
        var subEn = sub.Substitute(en.E);
        foreach (var s in TrSplitExpr(new BodyTranslationContext(false), subEn, etran, false, out _).Where(s => s.IsChecked)) {
          builder.Add(TrAssumeCmd(f.Origin, etran.CanCallAssumption(subEn, cco)));
          var constraint = Expression.CreateImplies(allOverrideEns, subEn);
          builder.Add(Assert(f.Origin, s.E, new FunctionContractOverride(true, constraint), builder.Context));
        }
      }
    }

    private void AddOverrideCheckTypeArgumentInstantiations(MemberDecl member, BoogieStmtListBuilder builder, Variables localVariables) {
      Contract.Requires(member is Function or MethodOrConstructor);
      Contract.Requires(member.EnclosingClass is TopLevelDeclWithMembers);
      Contract.Requires(builder != null);
      Contract.Requires(localVariables != null);

      MemberDecl overriddenMember;
      List<TypeParameter> overriddenTypeParameters;
      if (member is Function) {
        var o = ((Function)member).OverriddenFunction;
        overriddenMember = o;
        overriddenTypeParameters = o.TypeArgs;
      } else {
        var o = ((MethodOrConstructor)member).OverriddenMethod;
        overriddenMember = o;
        overriddenTypeParameters = o.TypeArgs;
      }
      var typeMap = GetTypeArgumentSubstitutionMap(overriddenMember, member);
      foreach (var tp in Util.Concat(overriddenMember.EnclosingClass.TypeArgs, overriddenTypeParameters)) {
        localVariables.GetOrAdd(BplLocalVar(NameTypeParam(tp), Predef.Ty, out var lhs));
        var rhs = TypeToTy(typeMap[tp]);
        builder.Add(new Boogie.AssumeCmd(tp.Origin, Boogie.Expr.Eq(lhs, rhs)));
      }
    }


    private void AddFunctionOverrideSubsetChk(Function func, BoogieStmtListBuilder builder, ExpressionTranslator etran, Variables localVariables,
      Dictionary<IVariable, Expression> substMap, Dictionary<TypeParameter, Type> typeMap) {
      //getting framePrime
      List<FrameExpression> traitFrameExps = [];
      FunctionCallSubstituter sub = new FunctionCallSubstituter(substMap, typeMap,
        (TraitDecl)func.OverriddenFunction.EnclosingClass, (TopLevelDeclWithMembers)func.EnclosingClass);
      foreach (var e in func.OverriddenFunction.Reads.Expressions) {
        var newE = sub.Substitute(e.E);
        FrameExpression fe = new FrameExpression(e.Origin, newE, e.FieldName);
        traitFrameExps.Add(fe);
      }

      QKeyValue kv = etran.TrAttributes(func.Attributes, null);

      IOrigin tok = func.Origin;
      // Declare a local variable $_ReadsFrame: [ref, Field]bool
      Bpl.IdentifierExpr traitFrame = etran.ReadsFrame(func.OverriddenFunction.Origin);  // this is a throw-away expression, used only to extract the type and name of the $_ReadsFrame variable
      traitFrame.Name = func.EnclosingClass.Name + "_" + traitFrame.Name;
      Contract.Assert(traitFrame.Type != null);  // follows from the postcondition of ReadsFrame
      var frame = localVariables.GetOrAdd(new Bpl.LocalVariable(tok, new Bpl.TypedIdent(tok, null ?? traitFrame.Name, traitFrame.Type)));
      // $_ReadsFrame := (lambda $o: ref, $f: Field :: $o != null && $Heap[$o,alloc] ==> ($o,$f) in Modifies/Reads-Clause);
      var oVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$o", Predef.RefType));
      var o = new Bpl.IdentifierExpr(tok, oVar);
      var fVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$f", Predef.FieldName(tok)));
      var f = new Bpl.IdentifierExpr(tok, fVar);
      Bpl.Expr ante = BplAnd(Bpl.Expr.Neq(o, Predef.Null), etran.IsAlloced(tok, o));
      Bpl.Expr consequent = InRWClause(tok, o, f, traitFrameExps, etran, null, null);
      Bpl.Expr lambda = new Bpl.LambdaExpr(tok, [], [oVar, fVar], null,
                                           BplImp(ante, consequent));

      //to initialize $_ReadsFrame variable to Frame'
      builder.Add(Bpl.Cmd.SimpleAssign(tok, new Bpl.IdentifierExpr(tok, frame), lambda));

      // emit: assert (forall o: ref, f: Field :: o != null && $Heap[o,alloc] && (o,f) in subFrame ==> $_ReadsFrame[o,f]);
      Bpl.Expr oInCallee = InRWClause(tok, o, f, func.Reads.Expressions, etran, null, null);
      Bpl.Expr consequent2 = InRWClause(tok, o, f, traitFrameExps, etran, null, null);
      Bpl.Expr q = new Bpl.ForallExpr(tok, [], [oVar, fVar],
                                      BplImp(BplAnd(ante, oInCallee), consequent2));
      var description = new TraitFrame(func.WhatKind, false, func.Reads.Expressions, traitFrameExps);
      builder.Add(Assert(tok, q, description, builder.Context, kv));
    }

    private void AddFunctionOverrideReqsChk(Function f, BoogieStmtListBuilder builder, ExpressionTranslator etran,
      Dictionary<IVariable, Expression> substMap, Dictionary<TypeParameter, Type> typeMap) {
      Contract.Requires(f != null);
      Contract.Requires(builder != null);
      Contract.Requires(etran != null);
      Contract.Requires(substMap != null);
      //generating trait pre-conditions with class variables
      var cco = new CanCallOptions(true, f, true);
      FunctionCallSubstituter sub = new FunctionCallSubstituter(substMap, typeMap,
        (TraitDecl)f.OverriddenFunction.EnclosingClass, (TopLevelDeclWithMembers)f.EnclosingClass);
      var subReqs = new List<Expression>();
      foreach (var req in ConjunctsOf(f.OverriddenFunction.Req)) {
        var subReq = sub.Substitute(req.E);
        builder.Add(TrAssumeCmd(f.Origin, etran.CanCallAssumption(subReq, cco)));
        builder.Add(TrAssumeCmdWithDependencies(etran, f.Origin, subReq, "overridden function requires clause"));
        subReqs.Add(subReq);
      }

      var allTraitReqs = subReqs.Aggregate((Expression)Expression.CreateBoolLiteral(f.Origin, true), (e0, e1) => Expression.CreateAnd(e0, e1));
      //generating class pre-conditions
      cco = new CanCallOptions(true, f);
      foreach (var req in ConjunctsOf(f.Req)) {
        foreach (var s in TrSplitExpr(new BodyTranslationContext(false), req.E, etran, false, out _).Where(s => s.IsChecked)) {
          builder.Add(TrAssumeCmd(f.Origin, etran.CanCallAssumption(req.E, cco)));
          var constraint = Expression.CreateImplies(allTraitReqs, req.E);
          builder.Add(Assert(f.Origin, s.E, new FunctionContractOverride(false, constraint), builder.Context));
        }
      }
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
      var forallFormals = new List<Boogie.Variable>();
      var argsJF = new List<Boogie.Expr>();
      var argsJFCanCall = new List<Boogie.Expr>();
      var argsCF = new List<Boogie.Expr>();
      var argsCFCanCall = new List<Boogie.Expr>();

      // Add type arguments
      forallFormals.AddRange(MkTyParamBinders(GetTypeParams(overridingFunction), out _));
      {
        var typeArguments = GetTypeArguments(f, overridingFunction).ConvertAll(TypeToTy);
        argsJF.AddRange(typeArguments);
        argsJFCanCall.AddRange(typeArguments);
        typeArguments = GetTypeArguments(overridingFunction, null).ConvertAll(TypeToTy);
        argsCF.AddRange(typeArguments);
        argsCFCanCall.AddRange(typeArguments);
      }

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
        argsJF.Add(layer);
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
        argsJF.Add(reveal);
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
        argsCF.Add(layer);
      }

      if (reveal != null) {
        argsCF.Add(reveal);
      }

      argsJF = Concat(argsJF, moreArgsJF);
      argsJFCanCall = Concat(argsJFCanCall, moreArgsJF);
      argsCF = Concat(argsCF, moreArgsCF);
      argsCFCanCall = Concat(argsCFCanCall, moreArgsCF);

      Bpl.Expr canCallFunc, canCallOverridingFunc;
      {
        var callName = new Bpl.IdentifierExpr(f.Origin, f.FullSanitizedName + "#canCall", Bpl.Type.Bool);
        canCallFunc = new Bpl.NAryExpr(f.Origin, new Bpl.FunctionCall(callName), argsJFCanCall);
        callName = new Bpl.IdentifierExpr(overridingFunction.Origin, overridingFunction.FullSanitizedName + "#canCall", Bpl.Type.Bool);
        canCallOverridingFunc = new Bpl.NAryExpr(f.Origin, new Bpl.FunctionCall(callName), argsCFCanCall);
      }

      // useViaCanCall: C.F#canCall(args)
      Bpl.Expr useViaCanCall = canCallFunc;

      // ante := C.F#canCall(args) || (J.F#canCall(args) && $Is(this, C))
      var ante = BplOr(canCallOverridingFunc, BplAnd(canCallFunc, isOfSubtype));

      Boogie.Expr funcAppl;
      {
        var funcID = new Boogie.IdentifierExpr(f.Origin, f.FullSanitizedName, TrType(f.ResultType));
        funcAppl = new Boogie.NAryExpr(f.Origin, new Boogie.FunctionCall(funcID), argsJF);
      }
      Boogie.Expr overridingFuncAppl;
      {
        var funcID = new Boogie.IdentifierExpr(overridingFunction.Origin, overridingFunction.FullSanitizedName, TrType(overridingFunction.ResultType));
        overridingFuncAppl = new Boogie.NAryExpr(overridingFunction.Origin, new Boogie.FunctionCall(funcID), argsCF);
      }

      // Build the triggers
      // { f'(Succ(s), args') }
      Boogie.Trigger tr = BplTriggerHeap(this, overridingFunction.Origin,
        overridingFuncAppl,
        readsHeap ? etran.HeapExpr : null);
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

    /// <summary>
    /// Return a type-parameter substitution map for function "f", as instantiated by the context of "overridingFunction".
    ///
    /// In more symbols, suppose "f" is declared as follows:
    ///     class/trait Tr[A,B] {
    ///       function f[C,D](...): ...
    ///     }
    /// and "overridingFunction" is declared as follows:
    ///     class/trait Cl[G] extends Tr[X(G),Y(G)] {
    ///       function f[R,S](...): ...
    ///     }
    /// Then, return the following map:
    ///     A -> X(G)
    ///     B -> Y(G)
    ///     C -> R
    ///     D -> S
    ///
    /// See also GetTypeArguments.
    /// </summary>
    private static Dictionary<TypeParameter, Type> GetTypeArgumentSubstitutionMap(MemberDecl member, MemberDecl overridingMember) {
      Contract.Requires(member is Function || member is MethodOrConstructor);
      Contract.Requires(overridingMember is Function || overridingMember is MethodOrConstructor);
      Contract.Requires(overridingMember.EnclosingClass is TopLevelDeclWithMembers);
      Contract.Requires(((ICallable)member).TypeArgs.Count == ((ICallable)overridingMember).TypeArgs.Count);

      var typeMap = new Dictionary<TypeParameter, Type>();

      var cl = (TopLevelDeclWithMembers)overridingMember.EnclosingClass;
      var classTypeMap = cl.ParentFormalTypeParametersToActuals;
      member.EnclosingClass.TypeArgs.ForEach(tp => typeMap.Add(tp, classTypeMap[tp]));

      var origTypeArgs = ((ICallable)member).TypeArgs;
      var overridingTypeArgs = ((ICallable)overridingMember).TypeArgs;
      for (var i = 0; i < origTypeArgs.Count; i++) {
        var otp = overridingTypeArgs[i];
        typeMap.Add(origTypeArgs[i], new UserDefinedType(otp.Origin, otp));
      }

      return typeMap;
    }

    private void AddMethodOverrideEnsChk(MethodOrConstructor m, BoogieStmtListBuilder builder, ExpressionTranslator etran,
      Dictionary<IVariable, Expression> substMap,
      Dictionary<TypeParameter, Type> typeMap) {
      Contract.Requires(m != null);
      Contract.Requires(builder != null);
      Contract.Requires(etran != null);
      Contract.Requires(substMap != null);
      //generating class post-conditions
      foreach (var en in ConjunctsOf(m.Ens)) {
        builder.Add(TrAssumeCmd(m.Origin, etran.CanCallAssumption(en.E)));
        builder.Add(TrAssumeCmdWithDependencies(etran, m.Origin, en.E, "overridden ensures clause"));
      }
      // conjunction of class post-conditions
      var allOverrideEns = m.Ens
        .Select(e => e.E)
        .Aggregate((Expression)Expression.CreateBoolLiteral(m.Origin, true), (e0, e1) => Expression.CreateAnd(e0, e1));
      //generating trait post-conditions with class variables
      FunctionCallSubstituter sub = new FunctionCallSubstituter(substMap, typeMap,
        (TraitDecl)m.OverriddenMethod.EnclosingClass, (TopLevelDeclWithMembers)m.EnclosingClass);
      foreach (var en in ConjunctsOf(m.OverriddenMethod.Ens)) {
        var subEn = sub.Substitute(en.E);
        foreach (var s in TrSplitExpr(new BodyTranslationContext(false), subEn, etran, false, out _).Where(s => s.IsChecked)) {
          builder.Add(TrAssumeCmd(m.OverriddenMethod.Origin, etran.CanCallAssumption(subEn)));
          var constraint = Expression.CreateImplies(allOverrideEns, subEn);
          builder.Add(Assert(m.Origin, s.E, new EnsuresStronger(constraint), builder.Context));
        }
      }
    }

    private void AddMethodOverrideReqsChk(MethodOrConstructor m, BoogieStmtListBuilder builder, ExpressionTranslator etran,
      Dictionary<IVariable, Expression> substMap,
      Dictionary<TypeParameter, Type> typeMap) {
      Contract.Requires(m != null);
      Contract.Requires(builder != null);
      Contract.Requires(etran != null);
      Contract.Requires(substMap != null);
      //generating trait pre-conditions with class variables
      FunctionCallSubstituter sub = new FunctionCallSubstituter(substMap, typeMap,
        (TraitDecl)m.OverriddenMethod.EnclosingClass, (TopLevelDeclWithMembers)m.EnclosingClass);
      var subReqs = new List<Expression>();
      foreach (var req in ConjunctsOf(m.OverriddenMethod.Req)) {
        var subReq = sub.Substitute(req.E);
        builder.Add(TrAssumeCmd(m.OverriddenMethod.Origin, etran.CanCallAssumption(subReq)));
        builder.Add(TrAssumeCmdWithDependencies(etran, m.Origin, subReq, "overridden requires clause"));
        subReqs.Add(subReq);
      }
      var allTraitReqs = subReqs.Aggregate((Expression)Expression.CreateBoolLiteral(m.Origin, true), (e0, e1) => Expression.CreateAnd(e0, e1));

      // generating class pre-conditions
      foreach (var req in ConjunctsOf(m.Req)) {
        foreach (var s in TrSplitExpr(new BodyTranslationContext(false), req.E, etran, false, out _).Where(s => s.IsChecked)) {
          builder.Add(TrAssumeCmd(m.Origin, etran.CanCallAssumption(req.E)));
          var constraint = Expression.CreateImplies(allTraitReqs, req.E);
          builder.Add(Assert(m.Origin, s.E, new RequiresWeaker(constraint), builder.Context));
        }
      }
    }

    private void AddOverrideTerminationChk(ICallable original, ICallable overryd, BoogieStmtListBuilder builder, ExpressionTranslator etran,
      Dictionary<IVariable, Expression> substMap, Dictionary<TypeParameter, Type> typeMap) {
      Contract.Requires(original != null);
      Contract.Requires(overryd != null);
      Contract.Requires(builder != null);
      Contract.Requires(etran != null);
      Contract.Requires(substMap != null);
      // Note, it is as if the trait's method is calling the class's method.
      var contextDecreases = overryd.Decreases.Expressions;
      var calleeDecreases = original.Decreases.Expressions;
      var T = (TraitDecl)((MemberDecl)overryd).EnclosingClass;
      var I = (TopLevelDeclWithMembers)((MemberDecl)original).EnclosingClass;

      // We want to check:  calleeDecreases <= contextDecreases (note, we can allow equality, since there is a bounded, namely 1, number of dynamic dispatches)
      if (Contract.Exists(contextDecreases, e => e is WildcardExpr)) {
        // no check needed
        return;
      }

      int N = Math.Min(contextDecreases.Count, calleeDecreases.Count);
      var toks = new List<IOrigin>();
      var callee = new List<Expr>();
      var caller = new List<Expr>();
      var calleeDafny = new List<Expression>();
      var callerDafny = new List<Expression>();
      FunctionCallSubstituter sub = new FunctionCallSubstituter(substMap, typeMap, T, I);

      for (int i = 0; i < N; i++) {
        Expression e0 = calleeDecreases[i];
        Expression e1 = sub.Substitute(contextDecreases[i]);
        if (!CompatibleDecreasesTypes(e0.Type, e1.Type)) {
          N = i;
          break;
        }
        toks.Add(new NestedOrigin(original.StartToken, e1.Origin));
        calleeDafny.Add(e0);
        callerDafny.Add(e1);
        callee.Add(etran.TrExpr(e0));
        caller.Add(etran.TrExpr(e1));
        var canCall = BplAnd(etran.CanCallAssumption(e1), etran.CanCallAssumption((e0)));
        builder.Add(new Bpl.AssumeCmd(e1.Origin, canCall));
      }

      var decrCountT = contextDecreases.Count;
      var decrCountC = calleeDecreases.Count;
      // Generally, we want to produce a check "decrClass <= decrTrait", allowing (the common case where) they are equal.
      // * If N < decrCountC && N < decrCountT, then "decrClass <= decrTrait" if the comparison ever gets beyond the
      //   parts that survived truncation.  Thus, we compare with "allowNoChange" set to "false".
      // Otherwise:
      // * If decrCountC == decrCountT, then the truncation we did above had no effect and we pass in "allowNoChange" as "true".
      // * If decrCountC > decrCountT, then we will have truncated decrClass above.  Let x,y and x' denote decrClass and
      //   decrTrait, respectively, where x and x' have the same length.  Considering how Dafny in effect pads the end of
      //   decreases tuples with a \top, we were supposed to evaluate (x,(y,\top)) <= (x',\top), which by lexicographic pairs
      //   we can expand to:
      //       x <= x' && (x == x' ==> (y,\top) <= \top)
      //   which is equivalent to just x <= x'.  Thus, we called DecreasesCheck to compare x and x' and we pass in "allowNoChange"
      //   as "true".
      // * If decrCountC < decrCountT, then we will have truncated decrTrait above.  Let x and x',y' denote decrClass and
      //   decrTrait, respectively, where x and x' have the same length.  We then want to check (x,\top) <= (x',(y',\top)), which
      //   expands to:
      //       x <= x' && (x == x' ==> \top <= (y',\top))
      //    =      { \top is strictly larger than a pair }
      //       x <= x' && (x == x' ==> false)
      //    =
      //       x < x'
      //   So we perform our desired check by calling DecreasesCheck to strictly compare x and x', so we pass in "allowNoChange"
      //   as "false".
      bool allowNoChange = N == decrCountT && decrCountT <= decrCountC;
      var decrChk = DecreasesCheck(toks, null, calleeDafny, callerDafny, callee, caller, null,
        null, allowNoChange, false);
      var assertedExpr = new DecreasesToExpr(
        Token.NoToken,
        contextDecreases.Select(sub.Substitute).ToList(),
        calleeDecreases,
        true);
      var desc = new TraitDecreases(original.WhatKind, assertedExpr);
      builder.Add(Assert(original.Origin, decrChk, desc, builder.Context));
    }

    private void AddMethodOverrideFrameSubsetChk(MethodOrConstructor m, bool isModifies, BoogieStmtListBuilder builder, ExpressionTranslator etran, Variables localVariables,
      Dictionary<IVariable, Expression> substMap,
      Dictionary<TypeParameter, Type> typeMap) {

      List<FrameExpression> classFrameExps;
      List<FrameExpression> originalTraitFrameExps;
      if (isModifies) {
        classFrameExps = m.Mod != null ? m.Mod.Expressions : [];
        originalTraitFrameExps = m.OverriddenMethod.Mod?.Expressions;
      } else {
        classFrameExps = m.Reads != null ? m.Reads.Expressions : [];
        originalTraitFrameExps = m.OverriddenMethod.Reads?.Expressions;
      }

      var traitFrameExps = new List<FrameExpression>();
      if (originalTraitFrameExps != null) {
        // Not currently possible for modifies, but is supported for reads
        if (originalTraitFrameExps.Any(e => e.E is WildcardExpr)) {
          // Trivially true
          return;
        }

        var sub = new FunctionCallSubstituter(substMap, typeMap, (TraitDecl)m.OverriddenMethod.EnclosingClass, (TopLevelDeclWithMembers)m.EnclosingClass);
        foreach (var e in originalTraitFrameExps) {
          var newE = sub.Substitute(e.E);
          var fe = new FrameExpression(e.Origin, newE, e.FieldName);
          traitFrameExps.Add(fe);
        }
      }

      var tok = m.Origin;
      var canCalls = traitFrameExps.Concat(classFrameExps)
        .Select(e => etran.CanCallAssumption(e.E))
        .Aggregate((Bpl.Expr)Bpl.Expr.True, BplAnd);
      builder.Add(TrAssumeCmd(tok, canCalls));

      var oVar = new Boogie.BoundVariable(tok, new Boogie.TypedIdent(tok, "$o", Predef.RefType));
      var o = new Boogie.IdentifierExpr(tok, oVar);
      var fVar = new Boogie.BoundVariable(tok, new Boogie.TypedIdent(tok, "$f", Predef.FieldName(tok)));
      var f = new Boogie.IdentifierExpr(tok, fVar);
      var ante = BplAnd(Boogie.Expr.Neq(o, Predef.Null), etran.IsAlloced(tok, o));

      // emit: assert (forall o: ref, f: Field :: o != null && $Heap[o,alloc] && (o,f) in subFrame ==> $_Frame[o,f]);
      var oInCallee = InRWClause(tok, o, f, classFrameExps, etran, null, null);
      var consequent2 = InRWClause(tok, o, f, traitFrameExps, etran, null, null);
      var q = new Boogie.ForallExpr(tok, [], [oVar, fVar],
        BplImp(BplAnd(ante, oInCallee), consequent2));
      var description = new TraitFrame(m.WhatKind, isModifies, classFrameExps, traitFrameExps);
      var kv = etran.TrAttributes(m.Attributes, null);
      builder.Add(Assert(m.Origin, q, description, builder.Context, kv));
    }

    // Return a way to know if an assertion should be converted to an assumption
    private void SetAssertionOnlyFilter(Node m) {
      List<TokenRange> rangesOnly = [];
      m.Visit(node => {
        if (node is AssertStmt assertStmt &&
            assertStmt.HasAssertOnlyAttribute(out var assertOnlyKind)) {
          var ifAfterLastToken = m.EndToken;
          if (rangesOnly.FindIndex(r => r.Contains(node.StartToken)) is var x && x >= 0) {
            if (assertOnlyKind == AssertStmt.AssertOnlyKind.Before) {// Just shorten the previous range
              rangesOnly[x] = new TokenRange(rangesOnly[x].StartToken, node.EndToken);
              return true;
            }

            ifAfterLastToken = rangesOnly[x].EndToken;
            rangesOnly.RemoveAt(x);
          }

          var rangeToAdd =
            assertOnlyKind == AssertStmt.AssertOnlyKind.Before ?
              new TokenRange(m.StartToken, assertStmt.EndToken) :
              assertOnlyKind == AssertStmt.AssertOnlyKind.After ?
              new TokenRange(assertStmt.StartToken, ifAfterLastToken)
              : assertStmt.EntireRange;
          if (assertOnlyKind == AssertStmt.AssertOnlyKind.Before && rangesOnly.Any(other => rangeToAdd.Intersects(other))) {
            // There are more precise ranges so we don't add this one
            return true;
          }
          rangesOnly.Add(rangeToAdd);
        }
        return true;
      });
      if (rangesOnly.Any()) {
        // TODO: What to do with refined postconditions?
        assertionOnlyFilter = token => rangesOnly.Any(range => range.Contains(token));
      }
    }

    private void ResetAssertionOnlyFilter() {
      assertionOnlyFilter = null;
    }

    /// <summary>
    /// This method is expected to be called at most once for each parameter combination, and in particular
    /// at most once for each value of "kind".
    /// </summary>
    private Boogie.Procedure AddMethod(MethodOrConstructor m, MethodTranslationKind kind) {
      Contract.Requires(m != null);
      Contract.Requires(m.EnclosingClass != null);
      Contract.Requires(Predef != null);
      Contract.Requires(currentModule == null && codeContext == null && IsAllocContext == null);
      Contract.Ensures(currentModule == null && codeContext == null && IsAllocContext == null);
      Contract.Ensures(Contract.Result<Boogie.Procedure>() != null);
      Contract.Assert(VisibleInScope(m));

      proofDependencies.SetCurrentDefinition(MethodVerboseName(m.FullDafnyName, kind), m);
      currentModule = m.EnclosingClass.EnclosingModuleDefinition;
      codeContext = m;
      IsAllocContext = new IsAllocContext(options, m.IsGhost);
      Boogie.Expr prevHeap = null;
      Boogie.Expr currHeap = null;
      var ordinaryEtran = new ExpressionTranslator(this, Predef, m.Origin, m);
      ExpressionTranslator etran;
      var inParams = new List<Boogie.Variable>();
      var bodyKind = kind == MethodTranslationKind.SpecWellformedness || kind == MethodTranslationKind.Implementation;
      if (m is TwoStateLemma) {
        var prevHeapVar = new Boogie.Formal(m.Origin, new Boogie.TypedIdent(m.Origin, "previous$Heap", Predef.HeapType), true);
        var currHeapVar = new Boogie.Formal(m.Origin, new Boogie.TypedIdent(m.Origin, "current$Heap", Predef.HeapType), true);
        inParams.Add(prevHeapVar);
        inParams.Add(currHeapVar);
        prevHeap = new Boogie.IdentifierExpr(m.Origin, prevHeapVar);
        currHeap = new Boogie.IdentifierExpr(m.Origin, currHeapVar);
        etran = new ExpressionTranslator(this, Predef, currHeap, prevHeap, m);
      } else {
        etran = ordinaryEtran;
      }

      GenerateMethodParameters(m.Origin, m, kind, etran, inParams, out var outParams);


      var name = MethodName(m, kind);
      var req = GetRequires();
      var mod = new List<Bpl.IdentifierExpr> { ordinaryEtran.HeapCastToIdentifierExpr };
      var ens = GetEnsures();
      var proc = new Bpl.Procedure(m.Origin, name, [],
        inParams, outParams.Values.ToList(), false, req, mod, ens, etran.TrAttributes(m.Attributes, null));
      AddVerboseNameAttribute(proc, m.FullDafnyName, kind);

      if (InsertChecksums) {
        InsertChecksum(m, proc, true);
      }

      currentModule = null;
      codeContext = null;
      IsAllocContext = null;

      return proc;

      List<Boogie.Requires> GetRequires() {
        var req = new List<Boogie.Requires>();
        // FREE PRECONDITIONS
        if (kind == MethodTranslationKind.SpecWellformedness || kind == MethodTranslationKind.Implementation || kind == MethodTranslationKind.OverrideCheck) {  // the other cases have no need for a free precondition
          if (m is TwoStateLemma) {
            // free requires prevHeap == Heap && HeapSucc(prevHeap, currHeap) && IsHeap(currHeap)
            var a0 = Boogie.Expr.Eq(prevHeap, ordinaryEtran.HeapExpr);
            var a1 = HeapSucc(prevHeap, currHeap);
            var a2 = FunctionCall(m.Origin, BuiltinFunction.IsGoodHeap, null, currHeap);
            req.Add(FreeRequires(m.Origin, BplAnd(a0, BplAnd(a1, a2)), null));
          }

          foreach (var typeBoundAxiom in TypeBoundAxioms(m.Origin, Concat(m.EnclosingClass.TypeArgs, m.TypeArgs))) {
            req.Add(Requires(m.Origin, true, null, typeBoundAxiom, null, null, null));
          }
        }
        if (m is TwoStateLemma) {
          // Checked preconditions that old parameters really existed in previous state
          var index = 0;
          foreach (var formal in m.Ins) {
            if (formal.IsOld) {
              var dafnyFormalIdExpr = new IdentifierExpr(formal.Origin, formal);
              var pIdx = m.Ins.Count == 1 ? "" : " at index " + index;
              var desc = new IsAllocated($"argument{pIdx} for parameter '{formal.Name}'",
                "in the two-state lemma's previous state" + IsAllocated.HelperFormal(formal),
                dafnyFormalIdExpr
              );
              var require = Requires(formal.Origin, false, null, MkIsAlloc(etran.TrExpr(dafnyFormalIdExpr), formal.Type, prevHeap),
                desc.FailureDescription, desc.SuccessDescription, null);
              require.Description = desc;
              req.Add(require);
            }
            index++;
          }
        }

        if (kind is MethodTranslationKind.SpecWellformedness or MethodTranslationKind.OverrideCheck) {
          return req;
        }

        // USER-DEFINED SPECIFICATIONS
        var comment = "user-defined preconditions";
        foreach (var p in ConjunctsOf(m.Req)) {
          var (errorMessage, successMessage) = CustomErrorMessage(p.Attributes);
          req.Add(FreeRequires(p.E.Origin, etran.CanCallAssumption(p.E), comment, true));
          comment = null;
          if (p.Label != null && kind == MethodTranslationKind.Implementation) {
            // don't include this precondition here, but record it for later use
            p.Label.E = (m is TwoStateLemma ? ordinaryEtran : etran.Old).TrExpr(p.E);
          } else {
            foreach (var s in TrSplitExprForMethodSpec(new BodyTranslationContext(m.ContainsHide), p.E, etran,
                       kind)) {
              if (s.IsOnlyChecked && bodyKind) {
                // don't include in split
              } else if (s.IsOnlyFree && !bodyKind) {
                // don't include in split -- it would be ignored, anyhow
              } else {
                req.Add(RequiresWithDependencies(s.Tok, s.IsOnlyFree, p.E, s.E, errorMessage, successMessage, null));
                // the free here is not linked to the free on the original expression (this is free things generated in the splitting.)
              }
            }
          }
        }

        // assume can-call conditions for the modifies clause
        comment = "user-defined frame expressions";
        foreach (var frameExpression in m.Mod.Expressions) {
          req.Add(FreeRequires(frameExpression.Origin, etran.CanCallAssumption(frameExpression.E), comment, true));
          comment = null;
        }

        return req;
      }

      List<Bpl.Ensures> GetEnsures() {
        var ens = new List<Bpl.Ensures>();
        if (kind is MethodTranslationKind.SpecWellformedness or MethodTranslationKind.OverrideCheck) {
          return ens;
        }

        // USER-DEFINED SPECIFICATIONS
        var comment = "user-defined postconditions";
        foreach (var p in ConjunctsOf(m.Ens)) {
          var (errorMessage, successMessage) = CustomErrorMessage(p.Attributes);
          AddEnsures(ens, FreeEnsures(p.E.Origin, etran.CanCallAssumption(p.E), comment, true));
          comment = null;
          foreach (var split in TrSplitExprForMethodSpec(new BodyTranslationContext(m.ContainsHide), p.E, etran, kind)) {
            var post = split.E;
            if (kind == MethodTranslationKind.Implementation && split.Tok.IsInherited(currentModule)) {
              // this postcondition was inherited into this module, so make it into the form "$_reverifyPost ==> s.E"
              post = BplImp(new Boogie.IdentifierExpr(split.E.tok, "$_reverifyPost", Boogie.Type.Bool), post);
            }
            if (split.IsOnlyFree && bodyKind) {
              // don't include in split -- it would be ignored, anyhow
            } else if (split.IsOnlyChecked && !bodyKind) {
              // don't include in split
            } else {
              AddEnsures(ens, EnsuresWithDependencies(split.Tok, split.IsOnlyFree || this.assertionOnlyFilter != null, p.E, post, errorMessage, successMessage, null));
            }
          }
        }
        if (m is Constructor && kind == MethodTranslationKind.Call) {
          var dafnyFresh = new OldExpr(Token.NoToken,
            new UnaryOpExpr(Token.NoToken, UnaryOpExpr.Opcode.Not,
              new UnaryOpExpr(Token.NoToken, UnaryOpExpr.Opcode.Allocated, new IdentifierExpr(Token.NoToken, "this"))));
          var fresh = Boogie.Expr.Not(etran.Old.IsAlloced(m.Origin, new Boogie.IdentifierExpr(m.Origin, "this", TrReceiverType(m))));
          AddEnsures(ens, Ensures(m.Origin, false || this.assertionOnlyFilter != null, dafnyFresh, fresh, null, null, "constructor allocates the object"));
        }
        foreach (BoilerplateTriple tri in GetTwoStateBoilerplate(m.Origin, m.Mod.Expressions, m.IsGhost, m.AllowsAllocation, ordinaryEtran.Old, ordinaryEtran, ordinaryEtran.Old)) {
          AddEnsures(ens, Ensures(tri.tok, tri.IsFree || this.assertionOnlyFilter != null, null, tri.Expr, tri.ErrorMessage, tri.SuccessMessage, tri.Comment));
        }

        // add the fuel assumption for the reveal method of a opaque method
        if (IsOpaqueRevealLemma(m)) {
          List<Expression> args = Attributes.FindExpressions(m.Attributes, "revealedFunction");
          if (args != null) {
            if (args[0].Resolved is MemberSelectExpr selectExpr) {
              var f = selectExpr.Member as Function;
              AddEnsures(ens, FreeEnsures(m.Origin, GetRevealConstant(f), null));
            }
          }
        }
        return ens;
      }
    }

    public static bool ModifiesClauseIsEmpty(Specification<FrameExpression> modifiesClause) {
      return modifiesClause.Expressions.All(e => e.E is SetDisplayExpr setDisplayExpr && !setDisplayExpr.Elements.Any());
    }

    private void InsertChecksum(MethodOrConstructor m, Boogie.Declaration decl, bool specificationOnly = false) {
      Contract.Requires(VisibleInScope(m));
      byte[] data;
      using (var writer = new System.IO.StringWriter()) {
        var printer = new Printer(writer, options);
        printer.PrintAttributes(m.Attributes, false, -1);
        printer.PrintFormals(m.Ins, m);
        if (m.Outs.Any()) {
          writer.Write("returns ");
          printer.PrintFormals(m.Outs, m);
        }
        printer.PrintSpec("", m.Req, 0);
        printer.PrintFrameSpecLine("", m.Mod, 0);
        printer.PrintSpec("", m.Ens, 0);
        printer.PrintDecreasesSpec(m.Decreases, 0);
        writer.WriteLine();
        if (!specificationOnly && m.Body != null && RevealedInScope(m)) {
          printer.PrintStatement(m.Body, 0);
        }
        data = Encoding.UTF8.GetBytes(writer.ToString());
      }

      InsertChecksum(decl, data);
    }

    internal IEnumerable<Bpl.Expr> TypeBoundAxioms(IOrigin tok, List<TypeParameter> typeParameters) {
      foreach (var typeParameter in typeParameters.Where(typeParameter => typeParameter.TypeBounds.Any())) {
        TypeBoundAxiomExpressions(tok, [], new UserDefinedType(typeParameter), typeParameter.TypeBounds,
          out var isBoxExpr, out var isAllocBoxExpr);
        yield return isBoxExpr;
        yield return isAllocBoxExpr;
      }
    }

    public void TypeBoundAxiomExpressions(IOrigin tok, List<Bpl.Variable> bvarsTypeParameters, Type type, List<Type> typeBounds,
      out Bpl.Expr isBoxExpr, out Bpl.Expr isAllocBoxExpr) {
      {
        // (forall bvarsTypeParameters, bx: Box ::
        //   { $IsBox(bx, typeExpression) }
        //   $IsBox(bx, typeExpression) ==>
        //     $IsBox(bx, Bound0) && $IsBox(bx, Bound1) && ...);
        var vars = new List<Bpl.Variable>();
        vars.AddRange(bvarsTypeParameters);
        var bx = BplBoundVar("bx", Predef.BoxType, vars);
        var isBox = MkIs(bx, TypeToTy(type), true);
        Bpl.Expr bounds = Bpl.Expr.True;
        foreach (var typeBound in typeBounds) {
          bounds = BplAnd(bounds, MkIs(bx, TypeToTy(typeBound), true));
        }

        var body = BplImp(isBox, bounds);
        isBoxExpr = new Bpl.ForallExpr(tok, vars, BplTrigger(isBox), body);
      }

      {
        // (forall bx: Box, $Heap: Heap ::
        //   { $IsAllocBox(bx, X, $h) }
        //   $IsAllocBox(bx, X, $h) && $IsGoodHeap($h) ==>
        //     $IsAllocBox(bx, Bound0, $h) && $IsAllocBox(bx, Bound1, $h) && ...);
        var vars = new List<Bpl.Variable>();
        vars.AddRange(bvarsTypeParameters);
        var bx = BplBoundVar("bx", Predef.BoxType, vars);
        var heap = BplBoundVar("$h", Predef.HeapType, vars);
        var isGoodHeap = FunctionCall(tok, BuiltinFunction.IsGoodHeap, null, heap);
        var isAllocBox = MkIsAlloc(bx, TypeToTy(type), heap, true);
        Bpl.Expr bounds = Bpl.Expr.True;
        foreach (var typeBound in typeBounds) {
          bounds = BplAnd(bounds, MkIsAlloc(bx, TypeToTy(typeBound), heap, true));
        }

        var body = BplImp(BplAnd(isAllocBox, isGoodHeap), bounds);
        isAllocBoxExpr = new Bpl.ForallExpr(tok, vars, BplTrigger(isAllocBox), body);
      }
    }
  }
}
