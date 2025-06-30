using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Diagnostics.Contracts;
using System.IO;
using System.Reflection;
using System.Security.Cryptography;
using Bpl = Microsoft.Boogie;
using BplParser = Microsoft.Boogie.Parser;
using System.Text;
using System.Text.RegularExpressions;
using System.Threading;
using Microsoft.Boogie;
using static Microsoft.Dafny.Util;
using Core;
using DafnyCore.Verifier;
using Microsoft.BaseTypes;
using Microsoft.Dafny.Compilers;
using Microsoft.Dafny.Triggers;
using Action = System.Action;
using PODesc = Microsoft.Dafny.ProofObligationDescription;
using static Microsoft.Dafny.GenericErrors;

namespace Microsoft.Dafny;

public partial class BoogieGenerator {

  private void AddArrowTypeAxioms(ArrowTypeDecl ad) {
    Contract.Requires(ad != null);
    var arity = ad.Arity;
    var tok = ad.Origin;

    // [Heap, Box, ..., Box]
    var mapArgs = Cons(Predef.HeapType, Map(Enumerable.Range(0, arity), i => Predef.BoxType));
    // [Heap, Box, ..., Box] Box
    var applyTy = new Bpl.MapType(tok, [], mapArgs, Predef.BoxType);
    // [Heap, Box, ..., Box] Bool
    var requiresTy = new Bpl.MapType(tok, [], mapArgs, Bpl.Type.Bool);
    // Set Box
    var objsetTy = TrType(program.SystemModuleManager.ObjectSetType());
    // [Heap, Box, ..., Box] (Set Box)
    var readsTy = new Bpl.MapType(tok, [], mapArgs, objsetTy);

    AddFunctionDeclaration(applyTy, requiresTy, readsTy, arity);

    // function ApplyN(Ty, ... Ty, HandleType, Heap, Box, ..., Box) : Box
    if (arity != 1) {  // Apply1 is already declared in DafnyPrelude.bpl
      SelectorFunction(null, Apply(arity), Predef.BoxType);
    }
    // function RequiresN(Ty, ... Ty, HandleType, Heap, Box, ..., Box) : Bool
    SelectorFunction(ad.Requires, Requires(arity), Bpl.Type.Bool);
    // function ReadsN(Ty, ... Ty, HandleType, Heap, Box, ..., Box) : Set Box
    SelectorFunction(ad.Reads, Reads(arity), objsetTy);

    SelectorSemantics(Apply(arity), Predef.BoxType, "h", applyTy, Requires(arity), requiresTy);
    SelectorSemantics(Requires(arity), Bpl.Type.Bool, "r", requiresTy, null, null);
    SelectorSemantics(Reads(arity), objsetTy, "rd", readsTy, null, null);

    UserSelectorFunction(Requires(ad.Arity), ad.Requires);
    UserSelectorFunction(Reads(ad.Arity), ad.Reads);

    AddFrameAxiom(ad, arity, tok, objsetTy);
    AddEmptyReadsPropertyForReadsAxiom(ad, arity, tok, objsetTy);
    AddEmptyReadsPropertyForRequiresAxiom(ad, arity, tok, objsetTy);
    AddIsBoxApplyAxiom(ad, arity, tok);
    AddIsAxiom(ad, arity, tok);
    AddIsAllocAxiom(ad, arity, tok);
    AddAllocatednessConsequenceAxiom(ad, arity, tok);

    return;

    // function {:inline true}
    //   FuncN._requires#canCall(G...G G: Ty, H:Heap, f:Handle, x ... x :Box): bool
    //   { true }
    // + similar for Reads
    void UserSelectorFunction(string fname, Function f) {
      var formals = new List<Bpl.Variable>();
      var rhsargs = new List<Bpl.Expr>();

      MapM(Enumerable.Range(0, arity + 1), i => rhsargs.Add(BplFormalVar("t" + i, Predef.Ty, true, formals)));

      var heap = BplFormalVar("heap", Predef.HeapType, true, formals);
      rhsargs.Add(heap);
      rhsargs.Add(BplFormalVar("f", Predef.HandleType, true, formals));

      MapM(Enumerable.Range(0, arity), i => rhsargs.Add(BplFormalVar("bx" + i, Predef.BoxType, true, formals)));

      sink.AddTopLevelDeclaration(new Bpl.Function(f.Origin, f.FullSanitizedName + "#canCall", [], formals,
        BplFormalVar(null, Bpl.Type.Bool, false), null,
        InlineAttribute(f.Origin)) { Body = Bpl.Expr.True });
    }

    // forall t1, .., tN+1 : Ty, p: [Heap, Box, ..., Box] Box, heap : Heap, b1, ..., bN : Box
    //      :: ApplyN(t1, .. tN+1, heap, HandleN(h, r, rd), b1, ..., bN) == h[heap, b1, ..., bN]
    //      :: RequiresN(t1, .. tN+1, heap, HandleN(h, r, rd), b1, ..., bN) <== r[heap, b1, ..., bN]
    //      :: ReadsN(t1, .. tN+1, heap, HandleN(h, r, rd), b1, ..., bN) == rd[heap, b1, ..., bN]
    void SelectorSemantics(string selector, Bpl.Type selectorTy, string selectorVar, Bpl.Type selectorVarTy, string precond, Bpl.Type precondTy) {
      Contract.Assert((precond == null) == (precondTy == null));
      var bvars = new List<Bpl.Variable>();

      var types = Map(Enumerable.Range(0, arity + 1), i => BplBoundVar("t" + i, Predef.Ty, bvars));

      var heap = BplBoundVar("heap", Predef.HeapType, bvars);

      var handleargs = new List<Bpl.Expr> { BplBoundVar("h", applyTy, bvars), BplBoundVar("r", requiresTy, bvars), BplBoundVar("rd", readsTy, bvars) };

      var boxes = Map(Enumerable.Range(0, arity), i => BplBoundVar("bx" + i, Predef.BoxType, bvars));

      var lhsargs = Concat(types, Cons(heap, Cons(FunctionCall(tok, Handle(arity), Predef.HandleType, handleargs), boxes)));
      Bpl.Expr lhs = FunctionCall(tok, selector, selectorTy, lhsargs);
      Func<Bpl.Expr, Bpl.Expr> pre = x => x;
      if (precond != null) {
        pre = x => FunctionCall(tok, precond, precondTy, lhsargs);
      }

      Bpl.Expr rhs = new Bpl.NAryExpr(tok, new Bpl.MapSelect(tok, arity + 1), Cons(new Bpl.IdentifierExpr(tok, selectorVar, selectorVarTy), Cons(heap, boxes)));
      Func<Bpl.Expr, Bpl.Expr, Bpl.Expr> op = Bpl.Expr.Eq;
      if (selectorVar == "rd") {
        var bx = BplBoundVar("bx", Predef.BoxType, bvars);
        lhs = IsSetMember(tok, lhs, bx, true);
        rhs = IsSetMember(tok, rhs, bx, true);
        // op = BplImp;
      }

      if (selectorVar == "r") {
        op = (u, v) => BplImp(v, u);
      }

      AddOtherDefinition(GetOrCreateTypeConstructor(ad), new Axiom(tok, BplForall(bvars, BplTrigger(lhs), op(lhs, rhs))));
    }

    void SelectorFunction(Function dafnyFunction, string name, Bpl.Type t) {
      var args = new List<Bpl.Variable>();
      MapM(Enumerable.Range(0, arity + 1), i => args.Add(BplFormalVar(null, Predef.Ty, true)));
      
      args.Add(BplFormalVar(null, Predef.HeapType, true));
      args.Add(BplFormalVar(null, Predef.HandleType, true));
      MapM(Enumerable.Range(0, arity), i => args.Add(BplFormalVar(null, Predef.BoxType, true)));
      var boogieFunction = new Bpl.Function(Token.NoToken, name, args, BplFormalVar(null, t, false));
      if (dafnyFunction != null) {
        declarationMapping[dafnyFunction] = boogieFunction;
      }

      sink.AddTopLevelDeclaration(boogieFunction);
    }
  }

  private void AddFunctionDeclaration(Bpl.MapType applyTy, Bpl.MapType requiresTy, Bpl.MapType readsTy, int arity) {
    // function HandleN([Heap, Box, ..., Box] Box, [Heap, Box, ..., Box] Bool) : HandleType
    var res = BplFormalVar(null, Predef.HandleType, true);
    var arg = new List<Bpl.Variable> {
      BplFormalVar(null, applyTy, true),
      BplFormalVar(null, requiresTy, true),
      BplFormalVar(null, readsTy, true)
    };
    var declaration = new Bpl.Function(Token.NoToken, Handle(arity), arg, res);
    sink.AddTopLevelDeclaration(declaration);
  }

  private void AddFrameAxiom(ArrowTypeDecl ad, int arity, IOrigin tok, Bpl.Type objsetTy) {
    // frame axiom
    /*

        forall t0..tN+1 : Ty, h0, h1 : Heap, f : Handle, bx1 .. bxN : Box,
          HeapSucc(h0, h1) && GoodHeap(h0) && GoodHeap(h1)
          && Is[&IsAllocBox](bxI, tI, h0)              // in h0, not hN
          && Is[&IsAlloc](f, Func(t1,..,tN, tN+1), h0) // in h0, not hN
          &&
          (forall o : ref::
               o != null [&& h0[o, alloc] && h1[o, alloc] &&]
               Reads(h,hN,bxs)[Box(o)]             // for hN in h0 and h1
            ==> h0[o,field] == h1[o,field])
        ==>  Reads(..h0..) == Reads(..h1..)
         AND Requires(f,h0,bxs) == Requires(f,h1,bxs) // which is needed for the next
         AND  Apply(f,h0,bxs) == Apply(f,h0,bxs)

         The [...] expressions are omitted for /allocated:0 and /allocated:1:
           - in these modes, functions are pure values and IsAlloc of a function is trivially true
           - o may be unallocated even if f reads it, so we require a stronger condition that
             even fields of *unallocated* objects o are unchanged from h0 to h1
           - given this stronger condition, we can say that f(bx1...bxN) does not change from h0 to h1
             even if some of bx1...bxN are unallocated
           - it's harder to satisfy the stronger condition, but two cases are nevertheless useful:
             1) f has an empty reads clause
             2) f explictly states that everything is its reads clause is allocated
       */
    {
      var bvars = new List<Bpl.Variable>();

      var types = Map(Enumerable.Range(0, arity + 1), i => BplBoundVar("t" + i, Predef.Ty, bvars));

      var h0 = BplBoundVar("h0", Predef.HeapType, bvars);
      var h1 = BplBoundVar("h1", Predef.HeapType, bvars);
      var heapSucc = HeapSucc(h0, h1);
      var goodHeaps = BplAnd(
        FunctionCall(tok, BuiltinFunction.IsGoodHeap, null, h0),
        FunctionCall(tok, BuiltinFunction.IsGoodHeap, null, h1));

      var f = BplBoundVar("f", Predef.HandleType, bvars);
      var boxes = Map(Enumerable.Range(0, arity), i => BplBoundVar("bx" + i, Predef.BoxType, bvars));

      var mkIs = MkIs(f, ClassTyCon(ad, types));
      var isness = BplAnd(
        Snoc(Map(Enumerable.Range(0, arity), i =>
            BplAnd(MkIs(boxes[i], types[i], true), Bpl.Expr.True)),
          BplAnd(mkIs, Bpl.Expr.True)));

      AddFrameForFunction(h0, Reads(ad.Arity));
      AddFrameForFunction(h1, Reads(ad.Arity));
      AddFrameForFunction(h0, Requires(ad.Arity));
      AddFrameForFunction(h1, Requires(ad.Arity));
      AddFrameForFunction(h0, Apply(ad.Arity));
      AddFrameForFunction(h1, Apply(ad.Arity));

      void AddFrameForFunction(Expr hN, string fname) {
        // inner forall vars
        var ivars = new List<Bpl.Variable>();
        var o = BplBoundVar("o", Predef.RefType, ivars);
        var fld = BplBoundVar("fld", Predef.FieldName(tok), ivars);

        var innerForall = new Bpl.ForallExpr(tok, [], ivars, BplImp(BplAnd(Bpl.Expr.Neq(o, Predef.Null),
            // Note, the MkIsAlloc conjunct of "isness" implies that everything in the reads frame is allocated in "h0", which by HeapSucc(h0,h1) also implies the frame is allocated in "h1"
            IsSetMember(tok, FunctionCall(tok, Reads(ad.Arity), objsetTy, Concat(types, Cons(hN, Cons(f, boxes)))),
              FunctionCall(tok, BuiltinFunction.Box, null, o), true)),
          Bpl.Expr.Eq(ReadHeap(tok, h0, o, fld), ReadHeap(tok, h1, o, fld))));

        sink.AddTopLevelDeclaration(new Axiom(tok,
          BplForall(bvars, new Bpl.Trigger(tok, true, new List<Bpl.Expr> { heapSucc, Fn(h1), mkIs }),
            BplImp(BplAnd(BplAnd(BplAnd(heapSucc, goodHeaps), isness), innerForall), Bpl.Expr.Eq(Fn(h0), Fn(h1)))), "frame axiom for " + fname));
        return;

        Expr Fn(Expr h) => FunctionCall(tok, fname, Bpl.Type.Bool, Concat(types, Cons(h, Cons<Bpl.Expr>(f, boxes))));
      }
    }
  }

  private void AddEmptyReadsPropertyForReadsAxiom(ArrowTypeDecl ad, int arity, IOrigin tok, Bpl.Type objsetTy) {
    /* axiom (forall T..: Ty, heap: Heap, f: HandleType, bx..: Box ::
       *   { ReadsN(T.., $OneHeap, f, bx..), $IsGoodHeap(heap) }
       *   { ReadsN(T.., heap, f, bx..) }
       *   $IsGoodHeap(heap) && Is...(f...bx...) ==>
       *   Set#Equal(ReadsN(T.., OneHeap, f, bx..), EmptySet) == Set#Equal(ReadsN(T.., heap, f, bx..), EmptySet));
       */
    {
      var bvars = new List<Bpl.Variable>();
      var types = Map(Enumerable.Range(0, arity + 1), i => BplBoundVar("t" + i, Predef.Ty, bvars));
      var oneheap = NewOneHeapExpr(tok);
      var h = BplBoundVar("heap", Predef.HeapType, bvars);
      var f = BplBoundVar("f", Predef.HandleType, bvars);
      var boxes = Map(Enumerable.Range(0, arity), i => BplBoundVar("bx" + i, Predef.BoxType, bvars));

      var goodHeap = FunctionCall(tok, BuiltinFunction.IsGoodHeap, null, h);

      var mkIs = MkIs(f, ClassTyCon(ad, types));
      var isness = BplAnd(
        Snoc(Map(Enumerable.Range(0, arity), i =>
            BplAnd(MkIs(boxes[i], types[i], true), Bpl.Expr.True)),
          BplAnd(mkIs, Bpl.Expr.True)));

      var readsOne = FunctionCall(tok, Reads(arity), objsetTy, Concat(types, Cons(oneheap, Cons(f, boxes))));
      var readsH = FunctionCall(tok, Reads(arity), objsetTy, Concat(types, Cons(h, Cons(f, boxes))));
      var empty = FunctionCall(tok, BuiltinFunction.SetEmpty, Predef.BoxType);
      var readsNothingOne = FunctionCall(tok, BuiltinFunction.SetEqual, null, readsOne, empty);
      var readsNothingH = FunctionCall(tok, BuiltinFunction.SetEqual, null, readsH, empty);

      sink.AddTopLevelDeclaration(new Axiom(tok, BplForall(bvars,
          new Bpl.Trigger(tok, true, new List<Bpl.Expr> { readsOne, goodHeap, mkIs },
            new Bpl.Trigger(tok, true, new List<Bpl.Expr> { readsH, mkIs })),
          BplImp(
            BplAnd(goodHeap, isness),
            BplIff(readsNothingOne, readsNothingH))),
        $"empty-reads property for {Reads(arity)} "));
    }
  }

  private void AddIsBoxApplyAxiom(ArrowTypeDecl ad, int arity, IOrigin tok) {
    // $Is and $IsAlloc axioms
    /*
        axiom (forall f: HandleType, t0: Ty, t1: Ty ::
          { $Is(f, Tclass._System.___hFunc1(t0, t1)) }
          $Is(f, Tclass._System.___hFunc1(t0, t1))
             <==> (forall h: Heap, bx0: Box ::
               { Apply1(t0, t1, f, h, bx0) }
               $IsGoodHeap(h) && $IsBox(bx0, t0)
               && precondition of f(bx0) holds in h
               ==> $IsBox(Apply1(t0, t1, f, h, bx0), t1)));
      */
    {
      var bvarsOuter = new List<Bpl.Variable>();
      var f = BplBoundVar("f", Predef.HandleType, bvarsOuter);
      var types = Map(Enumerable.Range(0, arity + 1), i => BplBoundVar("t" + i, Predef.Ty, bvarsOuter));
      var Is = MkIs(f, ClassTyCon(ad, types));

      var bvarsInner = new List<Bpl.Variable>();
      var h = BplBoundVar("h", Predef.HeapType, bvarsInner);
      var boxes = Map(Enumerable.Range(0, arity), i => BplBoundVar("bx" + i, Predef.BoxType, bvarsInner));
      var goodHeap = FunctionCall(tok, BuiltinFunction.IsGoodHeap, null, h);
      var isBoxes = BplAnd(Map(Enumerable.Range(0, arity), i => MkIs(boxes[i], types[i], true)));
      var pre = FunctionCall(tok, Requires(ad.Arity), Predef.BoxType, Concat(types, Cons(h, Cons(f, boxes))));
      var applied = FunctionCall(tok, Apply(ad.Arity), Predef.BoxType, Concat(types, Cons(h, Cons(f, boxes))));
      var appliedIs = MkIs(applied, types[ad.Arity], true);

      sink.AddTopLevelDeclaration(new Axiom(tok,
        BplForall(bvarsOuter, BplTrigger(Is),
          BplIff(Is,
            BplForall(bvarsInner, BplTrigger(applied),
              BplImp(BplAnd(BplAnd(goodHeap, isBoxes), pre), appliedIs))))));
    }
  }

  private void AddIsAxiom(ArrowTypeDecl ad, int arity, IOrigin tok) {
    /*
         axiom (forall f: HandleType, t0: Ty, t1: Ty, u0: Ty, u1: Ty ::
           { $Is(f, Tclass._System.___hFunc1(t0, t1)), $Is(f, Tclass._System.___hFunc1(u0, u1)) }
           $Is(f, Tclass._System.___hFunc1(t0, t1)) &&
           (forall bx: Box :: { $IsBox(bx, u0), $IsBox(bx, t0) }
               $IsBox(bx, u0) ==> $IsBox(bx, t0)) &&  // contravariant arguments
           (forall bx: Box :: { $IsBox(bx, t1), $IsBox(bx, u1) }
               $IsBox(bx, t1) ==> $IsBox(bx, u1))     // covariant result
           ==>
           $Is(f, Tclass._System.___hFunc1(u0, u1)));
      */
    {
      var bvarsOuter = new List<Bpl.Variable>();
      var f = BplBoundVar("f", Predef.HandleType, bvarsOuter);
      var typesT = Map(Enumerable.Range(0, arity + 1), i => BplBoundVar("t" + i, Predef.Ty, bvarsOuter));
      var IsT = MkIs(f, ClassTyCon(ad, typesT));
      var typesU = Map(Enumerable.Range(0, arity + 1), i => BplBoundVar("u" + i, Predef.Ty, bvarsOuter));
      var IsU = MkIs(f, ClassTyCon(ad, typesU));

      Func<Expr, Expr, Expr> Inner = (a, b) => {
        var bvarsInner = new List<Bpl.Variable>();
        var bx = BplBoundVar("bx", Predef.BoxType, bvarsInner);
        var isBoxA = MkIs(bx, a, true);
        var isBoxB = MkIs(bx, b, true);
        var tr = new Bpl.Trigger(tok, true, new[] { isBoxA }, new Bpl.Trigger(tok, true, new[] { isBoxB }));
        var imp = BplImp(isBoxA, isBoxB);
        return BplForall(bvarsInner, tr, imp);
      };

      var body = IsT;
      for (int i = 0; i < arity; i++) {
        body = BplAnd(body, Inner(typesU[i], typesT[i]));
      }
      body = BplAnd(body, Inner(typesT[arity], typesU[arity]));
      body = BplImp(body, IsU);
      sink.AddTopLevelDeclaration(new Axiom(tok,
        BplForall(bvarsOuter, new Bpl.Trigger(tok, true, new[] { IsT, IsU }), body)));
    }
  }

  private void AddIsAllocAxiom(ArrowTypeDecl ad, int arity, IOrigin tok) {
    /*  This is the definition of $IsAlloc function the arrow type:
        axiom (forall f: HandleType, t0: Ty, t1: Ty, h: Heap ::
          { $IsAlloc(f, Tclass._System.___hFunc1(t0, t1), h) }
          $IsGoodHeap(h)
          ==>
          (
            $IsAlloc(f, Tclass._System.___hFunc1(t0, t1), h)
              <==>
              (forall bx0: Box ::
                { Apply1(t0, t1, f, h, bx0) } { Reads1(t0, t1, f, h, bx0) }
                $IsBox(bx0, t0) && $IsAllocBox(bx0, t0, h)
                && precondition of f(bx0) holds in h
                ==>
                  (everything in reads set of f(bx0) is allocated in h)
          ));
        However, for /allocated:0 and /allocated:1, IsAlloc for arrow types is trivially true
        and implies nothing about the reads set.
      */
    {
      var bvarsOuter = new List<Bpl.Variable>();
      var f = BplBoundVar("f", Predef.HandleType, bvarsOuter);
      var types = Map(Enumerable.Range(0, arity + 1), i => BplBoundVar("t" + i, Predef.Ty, bvarsOuter));
      var h = BplBoundVar("h", Predef.HeapType, bvarsOuter);
      var goodHeap = FunctionCall(tok, BuiltinFunction.IsGoodHeap, null, h);
      var isAlloc = MkIsAlloc(f, ClassTyCon(ad, types), h);

      var bvarsInner = new List<Bpl.Variable>();
      var boxes = Map(Enumerable.Range(0, arity), i => BplBoundVar("bx" + i, Predef.BoxType, bvarsInner));
      var isAllocBoxes = BplAnd(Map(Enumerable.Range(0, arity), i =>
        BplAnd(MkIs(boxes[i], types[i], true), MkIsAlloc(boxes[i], types[i], h, true))));
      var pre = FunctionCall(tok, Requires(ad.Arity), Predef.BoxType, Concat(types, Cons(h, Cons<Bpl.Expr>(f, boxes))));
      var applied = FunctionCall(tok, Apply(ad.Arity), Predef.BoxType, Concat(types, Cons(h, Cons<Bpl.Expr>(f, boxes))));

      // (forall r: ref :: {Reads1(t0, t1, f, h, bx0)[$Box(r)]}  r != null && Reads1(t0, t1, f, h, bx0)[$Box(r)] ==> h[r, alloc])
      var bvarsR = new List<Bpl.Variable>();
      var r = BplBoundVar("r", Predef.RefType, bvarsR);
      var rNonNull = Bpl.Expr.Neq(r, Predef.Null);
      var reads = FunctionCall(tok, Reads(ad.Arity), Predef.BoxType, Concat(types, Cons(h, Cons<Bpl.Expr>(f, boxes))));
      var rInReads = IsSetMember(tok, reads, FunctionCall(tok, BuiltinFunction.Box, null, r), true);
      var rAlloc = IsAlloced(tok, h, r);
      var isAllocReads = BplForall(bvarsR, BplTrigger(rInReads), BplImp(BplAnd(rNonNull, rInReads), rAlloc));

      sink.AddTopLevelDeclaration(new Axiom(tok,
        BplForall(bvarsOuter, BplTrigger(isAlloc),
          BplImp(goodHeap,
            BplIff(isAlloc,
              BplForall(bvarsInner,
                new Bpl.Trigger(tok, true, new List<Bpl.Expr> { applied }, BplTrigger(reads)),
                BplImp(BplAnd(isAllocBoxes, pre), isAllocReads)))))));
    }
  }

  private void AddAllocatednessConsequenceAxiom(ArrowTypeDecl ad, int arity, IOrigin tok) {
    /*  This is the allocatedness consequence axiom of arrow types:
        axiom (forall f: HandleType, t0: Ty, t1: Ty, h: Heap ::
          { $IsAlloc(f, Tclass._System.___hFunc1(t0, t1), h) }
          $IsGoodHeap(h) &&
          $IsAlloc(f, Tclass._System.___hFunc1(t0, t1), h)
          ==>
              (forall bx0: Box ::
                { Apply1(t0, t1, f, h, bx0) }
                $IsAllocBox(bx0, t0, h)
                && precondition of f(bx0) holds in h
                ==>
                  $IsAllocBox(Apply1(t0, t1, f, h, bx0), t1, h))
          ));
      */
    {
      var bvarsOuter = new List<Bpl.Variable>();
      var f = BplBoundVar("f", Predef.HandleType, bvarsOuter);
      var types = Map(Enumerable.Range(0, arity + 1), i => BplBoundVar("t" + i, Predef.Ty, bvarsOuter));
      var h = BplBoundVar("h", Predef.HeapType, bvarsOuter);
      var goodHeap = FunctionCall(tok, BuiltinFunction.IsGoodHeap, null, h);
      var isAlloc = MkIsAlloc(f, ClassTyCon(ad, types), h);

      var bvarsInner = new List<Bpl.Variable>();
      var boxes = Map(Enumerable.Range(0, arity), i => BplBoundVar("bx" + i, Predef.BoxType, bvarsInner));
      var isAllocBoxes = BplAnd(Map(Enumerable.Range(0, arity), i => MkIsAlloc(boxes[i], types[i], h, true)));
      var pre = FunctionCall(tok, Requires(ad.Arity), Predef.BoxType, Concat(types, Cons(h, Cons<Bpl.Expr>(f, boxes))));
      var applied = FunctionCall(tok, Apply(ad.Arity), Predef.BoxType, Concat(types, Cons(h, Cons<Bpl.Expr>(f, boxes))));
      var appliedIsAlloc = MkIsAlloc(applied, types[ad.Arity], h, true);

      sink.AddTopLevelDeclaration(new Axiom(tok,
        BplForall(bvarsOuter, BplTrigger(isAlloc),
          BplImp(BplAnd(goodHeap, isAlloc),
            BplForall(bvarsInner, BplTrigger(applied),
              BplImp(BplAnd(isAllocBoxes, pre), appliedIsAlloc))))));
    }
  }

  private void AddEmptyReadsPropertyForRequiresAxiom(ArrowTypeDecl ad, int arity, IOrigin tok, Bpl.Type objsetTy) {
    /* axiom (forall T..: Ty, heap: Heap, f: HandleType, bx..: Box ::
       *   { RequiresN(T.., OneHeap, f, bx..), $IsGoodHeap(heap) }
       *   { RequiresN(T.., heap, f, bx..) }
       *   $IsGoodHeap(heap) && Is...(f...bx...) &&
       *   Set#Equal(ReadsN(T.., OneHeap, f, bx..), EmptySet)
       *   ==>
       *   RequiresN(T.., OneHeap, f, bx..) == RequiresN(T.., heap, f, bx..));
       */
    {
      var bvars = new List<Bpl.Variable>();
      var types = Map(Enumerable.Range(0, arity + 1), i => BplBoundVar("t" + i, Predef.Ty, bvars));
      var oneheap = NewOneHeapExpr(tok);
      var h = BplBoundVar("heap", Predef.HeapType, bvars);
      var f = BplBoundVar("f", Predef.HandleType, bvars);
      var boxes = Map(Enumerable.Range(0, arity), i => BplBoundVar("bx" + i, Predef.BoxType, bvars));

      var goodHeap = FunctionCall(tok, BuiltinFunction.IsGoodHeap, null, h);

      var mkIs = MkIs(f, ClassTyCon(ad, types));
      var isness = BplAnd(
        Snoc(Map(Enumerable.Range(0, arity), i =>
            BplAnd(MkIs(boxes[i], types[i], true), Bpl.Expr.True)),
          BplAnd(mkIs, Bpl.Expr.True)));

      var readsOne = FunctionCall(tok, Reads(arity), objsetTy, Concat(types, Cons(oneheap, Cons(f, boxes))));
      var empty = FunctionCall(tok, BuiltinFunction.SetEmpty, Predef.BoxType);
      var readsNothingOne = FunctionCall(tok, BuiltinFunction.SetEqual, null, readsOne, empty);

      var requiresOne = FunctionCall(tok, Requires(arity), Bpl.Type.Bool, Concat(types, Cons(oneheap, Cons(f, boxes))));
      var requiresH = FunctionCall(tok, Requires(arity), Bpl.Type.Bool, Concat(types, Cons(h, Cons(f, boxes))));

      sink.AddTopLevelDeclaration(new Axiom(tok, BplForall(bvars,
          new Bpl.Trigger(tok, true, new List<Bpl.Expr> { requiresOne, goodHeap, mkIs },
            new Bpl.Trigger(tok, true, new List<Bpl.Expr> { requiresH, mkIs })),
          BplImp(
            BplAnd(BplAnd(goodHeap, isness), readsNothingOne),
            Bpl.Expr.Eq(requiresOne, requiresH))),
        $"empty-reads property for {Requires(arity)}"));
    }
  }
}
