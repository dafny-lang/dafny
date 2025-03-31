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
    var map_args = Cons(Predef.HeapType, Map(Enumerable.Range(0, arity), i => Predef.BoxType));
    // [Heap, Box, ..., Box] Box
    var apply_ty = new Bpl.MapType(tok, [], map_args, Predef.BoxType);
    // [Heap, Box, ..., Box] Bool
    var requires_ty = new Bpl.MapType(tok, [], map_args, Bpl.Type.Bool);
    // Set Box
    var objset_ty = TrType(program.SystemModuleManager.ObjectSetType());
    // [Heap, Box, ..., Box] (Set Box)
    var reads_ty = new Bpl.MapType(tok, [], map_args, objset_ty);

    {
      // function HandleN([Heap, Box, ..., Box] Box, [Heap, Box, ..., Box] Bool) : HandleType
      var res = BplFormalVar(null, Predef.HandleType, true);
      var arg = new List<Bpl.Variable> {
          BplFormalVar(null, apply_ty, true),
          BplFormalVar(null, requires_ty, true),
          BplFormalVar(null, reads_ty, true)
        };
      var declaration = new Bpl.Function(Token.NoToken, Handle(arity), arg, res);
      sink.AddTopLevelDeclaration(declaration);
    }

    Action<Function, string, Bpl.Type> SelectorFunction = (dafnyFunction, name, t) => {
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
    };

    // function ApplyN(Ty, ... Ty, HandleType, Heap, Box, ..., Box) : Box
    if (arity != 1) {  // Apply1 is already declared in DafnyPrelude.bpl
      SelectorFunction(null, Apply(arity), Predef.BoxType);
    }
    // function RequiresN(Ty, ... Ty, HandleType, Heap, Box, ..., Box) : Bool
    SelectorFunction(ad.Requires, Requires(arity), Bpl.Type.Bool);
    // function ReadsN(Ty, ... Ty, HandleType, Heap, Box, ..., Box) : Set Box
    SelectorFunction(ad.Reads, Reads(arity), objset_ty);

    {
      // forall t1, .., tN+1 : Ty, p: [Heap, Box, ..., Box] Box, heap : Heap, b1, ..., bN : Box
      //      :: ApplyN(t1, .. tN+1, heap, HandleN(h, r, rd), b1, ..., bN) == h[heap, b1, ..., bN]
      //      :: RequiresN(t1, .. tN+1, heap, HandleN(h, r, rd), b1, ..., bN) <== r[heap, b1, ..., bN]
      //      :: ReadsN(t1, .. tN+1, heap, HandleN(h, r, rd), b1, ..., bN) == rd[heap, b1, ..., bN]
      Action<string, Bpl.Type, string, Bpl.Type, string, Bpl.Type> SelectorSemantics = (selector, selectorTy, selectorVar, selectorVarTy, precond, precondTy) => {
        Contract.Assert((precond == null) == (precondTy == null));
        var bvars = new List<Bpl.Variable>();

        var types = Map(Enumerable.Range(0, arity + 1), i => BplBoundVar("t" + i, Predef.Ty, bvars));

        var heap = BplBoundVar("heap", Predef.HeapType, bvars);

        var handleargs = new List<Bpl.Expr> {
            BplBoundVar("h", apply_ty, bvars),
            BplBoundVar("r", requires_ty, bvars),
            BplBoundVar("rd", reads_ty, bvars)
          };

        var boxes = Map(Enumerable.Range(0, arity), i => BplBoundVar("bx" + i, Predef.BoxType, bvars));

        var lhsargs = Concat(types, Cons(heap, Cons(FunctionCall(tok, Handle(arity), Predef.HandleType, handleargs), boxes)));
        Bpl.Expr lhs = FunctionCall(tok, selector, selectorTy, lhsargs);
        Func<Bpl.Expr, Bpl.Expr> pre = x => x;
        if (precond != null) {
          pre = x => FunctionCall(tok, precond, precondTy, lhsargs);
        }

        Bpl.Expr rhs = new Bpl.NAryExpr(tok, new Bpl.MapSelect(tok, arity + 1),
          Cons(new Bpl.IdentifierExpr(tok, selectorVar, selectorVarTy), Cons(heap, boxes)));
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
        AddOtherDefinition(GetOrCreateTypeConstructor(ad), new Axiom(tok,
          BplForall(bvars, BplTrigger(lhs), op(lhs, rhs))));
      };
      SelectorSemantics(Apply(arity), Predef.BoxType, "h", apply_ty, Requires(arity), requires_ty);
      SelectorSemantics(Requires(arity), Bpl.Type.Bool, "r", requires_ty, null, null);
      SelectorSemantics(Reads(arity), objset_ty, "rd", reads_ty, null, null);

      // function {:inline true}
      //   FuncN._requires#canCall(G...G G: Ty, H:Heap, f:Handle, x ... x :Box): bool
      //   { true }
      // + similar for Reads
      Action<string, Function> UserSelectorFunction = (fname, f) => {
        var formals = new List<Bpl.Variable>();
        var rhsargs = new List<Bpl.Expr>();

        MapM(Enumerable.Range(0, arity + 1), i => rhsargs.Add(BplFormalVar("t" + i, Predef.Ty, true, formals)));

        var heap = BplFormalVar("heap", Predef.HeapType, true, formals);
        rhsargs.Add(heap);
        rhsargs.Add(BplFormalVar("f", Predef.HandleType, true, formals));

        MapM(Enumerable.Range(0, arity), i => rhsargs.Add(BplFormalVar("bx" + i, Predef.BoxType, true, formals)));

        sink.AddTopLevelDeclaration(
          new Bpl.Function(f.Origin, f.FullSanitizedName + "#canCall", [], formals,
            BplFormalVar(null, Bpl.Type.Bool, false), null,
            InlineAttribute(f.Origin)) {
            Body = Bpl.Expr.True
          });
      };

      UserSelectorFunction(Requires(ad.Arity), ad.Requires);
      UserSelectorFunction(Reads(ad.Arity), ad.Reads);

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

        var isness = BplAnd(
          Snoc(Map(Enumerable.Range(0, arity), i =>
            BplAnd(MkIs(boxes[i], types[i], true), Bpl.Expr.True)),
          BplAnd(MkIs(f, ClassTyCon(ad, types)), Bpl.Expr.True)));

        Action<Bpl.Expr, string> AddFrameForFunction = (hN, fname) => {

          // inner forall vars
          var ivars = new List<Bpl.Variable>();
          var o = BplBoundVar("o", Predef.RefType, ivars);
          var fld = BplBoundVar("fld", Predef.FieldName(tok), ivars);

          var inner_forall = new Bpl.ForallExpr(tok, [], ivars, BplImp(
            BplAnd(
              Bpl.Expr.Neq(o, Predef.Null),
              // Note, the MkIsAlloc conjunct of "isness" implies that everything in the reads frame is allocated in "h0", which by HeapSucc(h0,h1) also implies the frame is allocated in "h1"
              IsSetMember(tok,
                FunctionCall(tok, Reads(ad.Arity), objset_ty, Concat(types, Cons(hN, Cons(f, boxes)))),
                FunctionCall(tok, BuiltinFunction.Box, null, o),
                true)
            ),
            Bpl.Expr.Eq(ReadHeap(tok, h0, o, fld), ReadHeap(tok, h1, o, fld))));

          Func<Bpl.Expr, Bpl.Expr> fn = h => FunctionCall(tok, fname, Bpl.Type.Bool, Concat(types, Cons(h, Cons<Bpl.Expr>(f, boxes))));

          sink.AddTopLevelDeclaration(new Axiom(tok,
            BplForall(bvars,
              new Bpl.Trigger(tok, true, new List<Bpl.Expr> { heapSucc, fn(h1) }),
              BplImp(
                BplAnd(BplAnd(BplAnd(heapSucc, goodHeaps), isness), inner_forall),
                Bpl.Expr.Eq(fn(h0), fn(h1)))), "frame axiom for " + fname));
        };

        AddFrameForFunction(h0, Reads(ad.Arity));
        AddFrameForFunction(h1, Reads(ad.Arity));
        AddFrameForFunction(h0, Requires(ad.Arity));
        AddFrameForFunction(h1, Requires(ad.Arity));
        AddFrameForFunction(h0, Apply(ad.Arity));
        AddFrameForFunction(h1, Apply(ad.Arity));
      }

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

        var isness = BplAnd(
          Snoc(Map(Enumerable.Range(0, arity), i =>
            BplAnd(MkIs(boxes[i], types[i], true), Bpl.Expr.True)),
          BplAnd(MkIs(f, ClassTyCon(ad, types)), Bpl.Expr.True)));

        var readsOne = FunctionCall(tok, Reads(arity), objset_ty, Concat(types, Cons(oneheap, Cons(f, boxes))));
        var readsH = FunctionCall(tok, Reads(arity), objset_ty, Concat(types, Cons(h, Cons(f, boxes))));
        var empty = FunctionCall(tok, BuiltinFunction.SetEmpty, Predef.BoxType);
        var readsNothingOne = FunctionCall(tok, BuiltinFunction.SetEqual, null, readsOne, empty);
        var readsNothingH = FunctionCall(tok, BuiltinFunction.SetEqual, null, readsH, empty);

        sink.AddTopLevelDeclaration(new Axiom(tok, BplForall(bvars,
          new Bpl.Trigger(tok, true, new List<Bpl.Expr> { readsOne, goodHeap },
          new Bpl.Trigger(tok, true, new List<Bpl.Expr> { readsH })),
          BplImp(
            BplAnd(goodHeap, isness),
            BplIff(readsNothingOne, readsNothingH))),
          string.Format("empty-reads property for {0} ", Reads(arity))));
      }

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

        var isness = BplAnd(
          Snoc(Map(Enumerable.Range(0, arity), i =>
            BplAnd(MkIs(boxes[i], types[i], true), Bpl.Expr.True)),
          BplAnd(MkIs(f, ClassTyCon(ad, types)), Bpl.Expr.True)));

        var readsOne = FunctionCall(tok, Reads(arity), objset_ty, Concat(types, Cons(oneheap, Cons(f, boxes))));
        var empty = FunctionCall(tok, BuiltinFunction.SetEmpty, Predef.BoxType);
        var readsNothingOne = FunctionCall(tok, BuiltinFunction.SetEqual, null, readsOne, empty);

        var requiresOne = FunctionCall(tok, Requires(arity), Bpl.Type.Bool, Concat(types, Cons(oneheap, Cons(f, boxes))));
        var requiresH = FunctionCall(tok, Requires(arity), Bpl.Type.Bool, Concat(types, Cons(h, Cons(f, boxes))));

        sink.AddTopLevelDeclaration(new Axiom(tok, BplForall(bvars,
          new Bpl.Trigger(tok, true, new List<Bpl.Expr> { requiresOne, goodHeap },
          new Bpl.Trigger(tok, true, new List<Bpl.Expr> { requiresH })),
          BplImp(
            BplAnd(BplAnd(goodHeap, isness), readsNothingOne),
            Bpl.Expr.Eq(requiresOne, requiresH))),
          string.Format("empty-reads property for {0}", Requires(arity))));
      }

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
        var pre = FunctionCall(tok, Requires(ad.Arity), Predef.BoxType, Concat(types, Cons(h, Cons<Bpl.Expr>(f, boxes))));
        var applied = FunctionCall(tok, Apply(ad.Arity), Predef.BoxType, Concat(types, Cons(h, Cons<Bpl.Expr>(f, boxes))));
        var applied_is = MkIs(applied, types[ad.Arity], true);

        sink.AddTopLevelDeclaration(new Axiom(tok,
          BplForall(bvarsOuter, BplTrigger(Is),
            BplIff(Is,
              BplForall(bvarsInner, BplTrigger(applied),
                BplImp(BplAnd(BplAnd(goodHeap, isBoxes), pre), applied_is))))));
      }
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
        var applied_isAlloc = MkIsAlloc(applied, types[ad.Arity], h, true);

        sink.AddTopLevelDeclaration(new Axiom(tok,
          BplForall(bvarsOuter, BplTrigger(isAlloc),
            BplImp(BplAnd(goodHeap, isAlloc),
              BplForall(bvarsInner, BplTrigger(applied),
                BplImp(BplAnd(isAllocBoxes, pre), applied_isAlloc))))));
      }
    }
  }

  private string AddTyAxioms(TopLevelDecl td) {
    Contract.Requires(td != null);
    IOrigin tok = td.Origin;

    // use the internal type synonym, if any
    if (!RevealedInScope(td) && td is RevealableTypeDecl revealableTypeDecl) {
      td = revealableTypeDecl.SelfSynonymDecl();
    }
    Contract.Assume(td is SubsetTypeDecl or not TypeSynonymDecl); // this is expected of the caller

    var func = GetOrCreateTypeConstructor(td);
    var name = func.Name;

    // Produce uniqueness or injectivity axioms, unless the type is one that may (non-uniquely) stand for another type.
    if (td is not AbstractTypeDecl and not InternalTypeSynonymDecl) {
      var tagAxiom = CreateTagAndCallingForTypeConstructor(td);
      AddOtherDefinition(func, tagAxiom);

      // Create the injectivity axiom and its function
      /*
         function List_0(Ty) : Ty;
         axiom (forall t0: Ty :: { List(t0) } List_0(List(t0)) == t0);
      */
      for (int i = 0; i < func.InParams.Count; i++) {
        var args = MkTyParamBinders(td.TypeArgs, out var argExprs);
        var inner = FunctionCall(tok, name, Predef.Ty, argExprs);
        Bpl.Variable tyVarIn = BplFormalVar(null, Predef.Ty, true);
        Bpl.Variable tyVarOut = BplFormalVar(null, Predef.Ty, false);
        var injname = name + "_" + i;
        var injfunc = new Bpl.Function(tok, injname, Singleton(tyVarIn), tyVarOut);
        sink.AddTopLevelDeclaration(injfunc);
        var outer = FunctionCall(tok, injname, args[i].TypedIdent.Type, inner);
        Bpl.Expr qq = BplForall(args, BplTrigger(inner), Bpl.Expr.Eq(outer, argExprs[i]));
        var injectivityAxiom = new Axiom(tok, qq, name + " injectivity " + i);
        AddOtherDefinition(injfunc, injectivityAxiom);
      }
    }

    // Boxing axiom (important for the properties of unbox)
    /*
       axiom (forall T: Ty, bx: Box ::
         { $IsBox(bx, List(T)) }
         $IsBox(bx, List(T))
            ==> $Box($Unbox(bx): DatatypeType) == bx
             && $Is($Unbox(bx): DatatypeType, List(T)));
    */
    if (!ModeledAsBoxType(UserDefinedType.FromTopLevelDecl(td.Origin, td))) {
      var args = MkTyParamBinders(td.TypeArgs, out var argExprs);
      var ty_repr = TrType(UserDefinedType.FromTopLevelDecl(td.Origin, td));
      var typeTerm = FunctionCall(tok, name, Predef.Ty, argExprs);
      AddBoxUnboxAxiom(tok, name, typeTerm, ty_repr, args);
    }

    return name;
  }

  /* Create the Tag and calling Tag on this type constructor
   *
   * The common case:
   *     const unique TagList: TyTag;
   *     const unique tytagFamily$List: TyTagFamily;  // defined once for each type named "List"
   *     axiom (forall t0: Ty :: { List(t0) } Tag(List(t0)) == TagList && TagFamily(List(t0)) == tytagFamily$List);
   * For types obtained via an abstract import, just do:
   *     const unique tytagFamily$List: TyTagFamily;  // defined once for each type named "List"
   *     axiom (forall t0: Ty :: { List(t0) } TagFamily(List(t0)) == tytagFamily$List);
   */
  private Axiom CreateTagAndCallingForTypeConstructor(TopLevelDecl td) {
    IOrigin tok = td.Origin;
    var inner_name = GetClass(td).TypedIdent.Name;
    string name = "T" + inner_name;

    var args = MkTyParamBinders(td.TypeArgs, out var argExprs);
    var inner = FunctionCall(tok, name, Predef.Ty, argExprs);
    Bpl.Expr body = Bpl.Expr.True;

    if (!td.EnclosingModuleDefinition.IsFacade) {
      var tagName = "Tag" + inner_name;
      var tag = new Bpl.Constant(tok, new Bpl.TypedIdent(tok, tagName, Predef.TyTag), true);
      sink.AddTopLevelDeclaration(tag);
      body = Bpl.Expr.Eq(FunctionCall(tok, "Tag", Predef.TyTag, inner), new Bpl.IdentifierExpr(tok, tag));
    }

    if (!tytagConstants.TryGetValue(td.Name, out var tagFamily)) {
      tagFamily = new Bpl.Constant(Token.NoToken,
        new Bpl.TypedIdent(Token.NoToken, "tytagFamily$" + td.Name, Predef.TyTagFamily), true);
      tytagConstants.Add(td.Name, tagFamily);
    }

    body = BplAnd(body,
      Bpl.Expr.Eq(FunctionCall(tok, "TagFamily", Predef.TyTagFamily, inner), new Bpl.IdentifierExpr(tok, tagFamily)));

    var qq = BplForall(args, BplTrigger(inner), body);
    var tagAxiom = new Axiom(tok, qq, name + " Tag");
    return tagAxiom;
  }

  private void AddBitvectorTypeAxioms(int w) {
    Contract.Requires(0 <= w);

    if (w == 0) {
      // the axioms for bv0 are already in DafnyPrelude.bpl
      return;
    }

    // box/unbox axiom
    var tok = Token.NoToken;
    var printableName = "bv" + w;
    var dafnyType = new BitvectorType(options, w);
    var boogieType = BplBvType(w);
    var typeTerm = TypeToTy(dafnyType);
    AddBoxUnboxAxiom(tok, printableName, typeTerm, boogieType, []);

    // axiom (forall v: bv3 :: { $Is(v, TBitvector(3)) } $Is(v, TBitvector(3)));
    var vVar = BplBoundVar("v", boogieType, out var v);
    var bvs = new List<Variable>() { vVar };
    var isBv = MkIs(v, typeTerm);
    var tr = BplTrigger(isBv);
    sink.AddTopLevelDeclaration(new Bpl.Axiom(tok, new Bpl.ForallExpr(tok, bvs, tr, isBv)));

    // axiom (forall v: bv3, heap: Heap :: { $IsAlloc(v, TBitvector(3), h) } $IsAlloc(v, TBitvector(3), heap));
    vVar = BplBoundVar("v", boogieType, out v);
    var heapVar = BplBoundVar("heap", Predef.HeapType, out var heap);
    bvs = [vVar, heapVar];
    var isAllocBv = MkIsAlloc(v, typeTerm, heap);
    tr = BplTrigger(isAllocBv);
    sink.AddTopLevelDeclaration(new Bpl.Axiom(tok, new Bpl.ForallExpr(tok, bvs, tr, isAllocBv)));
  }

  /// <summary>
  /// Generate:
  ///     axiom (forall args: Ty, bx: Box ::
  ///       { $IsBox(bx, name(argExprs)) }
  ///       $IsBox(bx, name(argExprs)) ==>
  ///         $Box($Unbox(bx): tyRepr) == bx &&
  ///         $Is($Unbox(bx): tyRepr, name(argExprs)));
  /// </summary>
  private void AddBoxUnboxAxiom(IOrigin tok, string printableName, Bpl.Expr typeTerm, Bpl.Type tyRepr, List<Variable> args) {
    Contract.Requires(tok != null);
    Contract.Requires(printableName != null);
    Contract.Requires(typeTerm != null);
    Contract.Requires(tyRepr != null);
    Contract.Requires(args != null);

    var bxVar = BplBoundVar("bx", Predef.BoxType, out var bx);
    var unbox = FunctionCall(tok, BuiltinFunction.Unbox, tyRepr, bx);
    var box_is = MkIs(bx, typeTerm, true);
    var unbox_is = MkIs(unbox, typeTerm, false);
    var box_unbox = FunctionCall(tok, BuiltinFunction.Box, null, unbox);
    sink.AddTopLevelDeclaration(
      new Axiom(tok,
        BplForall(Snoc(args, bxVar), BplTrigger(box_is),
          BplImp(box_is, BplAnd(Bpl.Expr.Eq(box_unbox, bx), unbox_is))),
        "Box/unbox axiom for " + printableName));
  }

  /// <summary>
  /// See GeneratePartialGuesses for an example of how GenerateAndCheckGuesses emits.
  /// </summary>
  private void GenerateAndCheckGuesses(IOrigin tok, List<BoundVar> bvars, List<BoundedPool> bounds, Expression expr,
    Attributes triggerAttributes, bool autoTriggerSearchFailed, BoogieStmtListBuilder builder, ExpressionTranslator etran) {
    Contract.Requires(tok != null);
    Contract.Requires(bvars != null);
    Contract.Requires(bounds != null);
    Contract.Requires(expr != null);
    Contract.Requires(builder != null);
    Contract.Requires(etran != null);

    List<(List<(BoundVar, Expression)>, Expression)> partialGuesses = GeneratePartialGuesses(bvars, expr);
    Bpl.Expr w = Bpl.Expr.False;
    foreach (var tup in partialGuesses) {
      var body = etran.TrExpr(tup.Item2);
      Bpl.Expr typeConstraints = Bpl.Expr.True;
      var undetermined = new List<BoundVar>();
      var substMap = new Dictionary<IVariable, Expression>();
      foreach (var be in tup.Item1) {
        if (be.Item2 == null) {
          undetermined.Add(be.Item1);
        } else {
          substMap.Add(be.Item1, be.Item2);
          typeConstraints = BplAnd(typeConstraints, MkIs(etran.TrExpr(be.Item2), be.Item1.Type));
        }
      }
      var canCalls = etran.CanCallAssumption(tup.Item2);
      body = BplImp(canCalls, body);
      body = BplAnd(typeConstraints, body);

      if (undetermined.Count != 0) {
        List<bool> freeOfAlloc = BoundedPool.HasBounds(bounds, BoundedPool.PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc);
        var bvs = new List<Variable>();
        var typeAntecedent = etran.TrBoundVariables(undetermined, bvs, false, freeOfAlloc);
        var triggers = TrTrigger(etran, triggerAttributes, tok, substMap, undetermined);
        body = new Bpl.ExistsExpr(tok, bvs, triggers, BplAnd(typeAntecedent, body));
      }
      w = BplOr(body, w);
    }
    builder.Add(Assert(tok, w, new LetSuchThatExists(bvars, expr, autoTriggerSearchFailed), builder.Context));
  }

  /// <summary>
  /// Take a linear scan through the bound variables, for each one considering specific guesses.
  /// Then, fill in "expression" with those guesses, remembering which variables have been substituted for what.
  /// What's returned is a list of tuples of the form (substitutionMappings, expressionWithSubstitutions).
  ///
  /// In substitutionMappings, a mapping "x := null" says for the caller to quantify over "x".
  /// Any non-null mappings, say "x := e0, y := e1" say that "x" and "y" have been replaced by "e0" and "e1" in "expression"
  /// to form "expressionWithSubstitutions".
  /// 
  /// The reason for returning substitutionMappings rather than just a list of variables is so that the caller can
  /// apply these substitutions in triggers that were computed for the entire "expression". Therefore, each non-null
  /// mapping "x := e" is one where "e" is acceptable in a trigger. 
  ///
  /// Here is an example. Assuming that the types of a,b,c are nonempty and that we obtain
  ///
  ///   GuessWitnesses(c):  0, a, b
  ///   GuessWitnesses(b):  10
  ///   GuessWitnesses(a):  88
  ///  
  /// then GeneratePartialGuesses works as follows:
  ///
  ///   GeneratePartialGuesses([a, b, c], X || Y(a) || Z(a, c)) {
  ///     yield ([], X) // since X does not mention a or b or c
  /// 
  ///     GeneratePartialGuesses([b, c], Y(a) || Z(a, c)) {
  ///       yield ([], Y(a)) // since Y(a) does not mention b or c
  /// 
  ///       GeneratePartialGuesses([c], Z(a, c)) {
  ///         GeneratePartialGuesses([], Z(a, c)) {
  ///           yield ([], Z(a, c)) // no vars
  ///         }
  /// 
  ///         yield ([c:=null], Z(a, c)) // quantify over c
  ///         yield ([c:=0], Z(a, 0)) // guess c := 0
  ///         yield ([c:=a], Z(a, a)) // guess c := a
  ///         yield ([c:=b], Z(a, b)) // guess c := b
  ///       }
  ///
  ///       yield ([c:=null], Z(a, c)) // since b does not occur in expression
  ///       yield ([c:=0], Z(a, 0)) // since b does not occur in expression
  ///       yield ([c:=a], Z(a, a)) // since b does not occur in expression
  ///       yield ([b:=null, c:=b], Z(a, b)) // quantify over b
  ///       yield ([b:=10, c:=10], Z(a, 10)) // guess b := 10
  ///     }
  ///
  ///     yield ([a:=null], Y(a)) // quantify over a
  ///     yield ([a:=88], Y(88)) // guess a := 88
  ///  
  ///     yield ([a:=null, c:=null], Z(a, c)) // quantify over a
  ///     yield ([a:=88, c:=null], Z(88, c)) // guess a := 88
  ///
  ///     yield ([a:=null, c:=0], Z(a, 0)) // quantify over a
  ///     yield ([a:=88, c:=0], Z(88, 0)) // guess a := 88
  ///
  ///     yield ([a:=null, c:=a], Z(a, a)) // quantify over a
  ///     yield ([a:=88, c:=88], Z(88, 88)) // guess a := 88
  ///
  ///     yield ([a:=null, b:=null, c:=b], Z(a, b)) // quantify over a
  ///     yield ([a:=88, b:=null, c:=b], Z(88, b)) // guess a := 88
  ///
  ///     yield ([a:=null, b:=10, c:=10], Z(a, 10)) // quantify over a
  ///     yield ([a:=88, b:=10, c:=10], Z(88, 10)) // guess a := 88
  ///   }
  ///
  /// From these yields, the caller (GenerateAndCheckGuesses) will then emit the following disjuncts:
  /// 
  ///   XCallCall ==> X
  /// 
  ///   exists a :: Is(a, A) && (YCanCall(a) ==> Y(a))
  ///   YCanCall(88) ==> Y(88)
  /// 
  ///   exists a, c :: Is(a, A) && Is(c, C) && (ZCanCall(a, b) ==> Z(a, c))
  ///   exists c :: Is(c, C) && (ZCanCall(88, c) ==> Z(88, c))
  /// 
  ///   exists a :: Is(a, A) && (ZCanCall(a, 0) ==> Z(a, 0))
  ///   ZCanCall(88, 0) ==> Z(88, 0)
  ///
  ///   exists a :: Is(a, A) && (ZCanCall(a, a) ==> Z(a, a))
  ///   ZCanCall(88, 88) ==> Z(88, 88)
  ///
  ///   exists a, b :: Is(a, A) && Is(b, B) && (ZCanCall(a, b) ==> Z(a, b))
  ///   exists b :: Is(b, B) && (ZCanCall ==> Z(88, b))
  ///
  ///   exists a :: Is(a, A) && (ZCanCall(a, 10) ==> Z(a, 10))
  ///   ZCanCall(88, 10) ==> Z(88, 10)
  /// </summary>
  List<(List<(BoundVar, Expression)>, Expression)> GeneratePartialGuesses(List<BoundVar> bvars, Expression expression) {
    if (bvars.Count == 0) {
      var tup = (new List<(BoundVar, Expression)>(), expression);
      return [tup];
    }

    var result = new List<(List<(BoundVar, Expression)>, Expression)>();

    var (exprIndependentOfVars, exprMentionsVars) = SeparateDisjunctsAccordingToVariableUsage(bvars, expression);
    if (!LiteralExpr.IsFalse(exprIndependentOfVars)) {
      var tup = (new List<(BoundVar, Expression)>(), exprIndependentOfVars);
      result.Add(tup);
      expression = exprMentionsVars;
    }

    var x = bvars[0];
    var otherBvars = bvars.GetRange(1, bvars.Count - 1);
    foreach (var tup in GeneratePartialGuesses(otherBvars, expression)) {
      // in the special case that x does not even occur in expression (and we know the type has a value for x), we can just ignore x
      if (!FreeVariablesUtil.ContainsFreeVariable(tup.Item2, false, x) && x.Type.KnownToHaveToAValue(x.IsGhost)) {
        result.Add(tup);
        continue;
      }

      // one possible result is to quantify over x
      var vs = new List<(BoundVar, Expression)>() { (x, null) };
      vs.AddRange(tup.Item1);
      result.Add((vs, tup.Item2));

      // other possibilities involve guessing a value for x
      foreach (var guess in GuessWitnesses(x, tup.Item2)) {
        var g = Substitute(tup.Item2, x, guess);
        vs = [(x, guess)];
        AddRangeSubst(vs, tup.Item1, x, guess);
        result.Add((vs, g));
      }
    }
    return result;
  }

  /// <summary>
  /// Return a pair of expressions (a, b) such that the disjunction "a || b" is equivalent to "expression"
  /// and expression "a" does not mention any variable in "vars".
  /// Expression "a" is always returned as "false" unless the types of all variables in "vars" are known to have a value.
  /// </summary>
  (Expression, Expression) SeparateDisjunctsAccordingToVariableUsage(List<BoundVar> vars, Expression expression) {
    Expression a = Expression.CreateBoolLiteral(expression.Origin, false);

    if (vars.Any(x => !x.Type.KnownToHaveToAValue(x.IsGhost))) {
      return (a, expression);
    }

    // Place the left-most var-independent disjuncts into "a" and the rest into "b". 
    // The loop below has the effect of:
    //         var d: List<Expression> := Expression.Disjuncts(expression);
    //         var (prefix, rest) :|
    //             "prefix" is the longest prefix of "d" where no Expression mentions a variable in "vars" and
    //             "rest" is the remaining Expression's of "d";
    //         return (Or(prefix), Or(rest));
    // But the loop optimizes the case where "prefix" is empty, returning "(false, expression)" in the event
    // that the first element of "d" contains some variable in "vars".
    Expression b = Expression.CreateBoolLiteral(expression.Origin, false);
    var seenDisjunctsWithoutVariables = false;
    var seenDisjunctsWithVariables = false;
    foreach (var disjunct in Expression.Disjuncts(expression)) {
      if (!seenDisjunctsWithVariables && !vars.Any(x => FreeVariablesUtil.ContainsFreeVariable(disjunct, false, x))) {
        a = Expression.CreateOr(a, disjunct);
        seenDisjunctsWithoutVariables = true;
      } else if (!seenDisjunctsWithoutVariables) {
        // everything goes into the second component, so no need to split up into new disjunction
        return (a, expression);
      } else {
        b = Expression.CreateOr(b, disjunct);
        seenDisjunctsWithVariables = true;
      }
    }

    return (a, b);
  }

  private void AddRangeSubst(List<(BoundVar, Expression)> vs, List<(BoundVar, Expression)> aa, IVariable v, Expression e) {
    Contract.Requires(vs != null);
    Contract.Requires(aa != null);
    Contract.Requires(v != null);
    Contract.Requires(e != null);
    foreach (var be in aa) {
      if (be.Item2 == null) {
        vs.Add(be);
      } else {
        vs.Add((be.Item1, Substitute(be.Item2, v, e)));
      }
    }
  }

  IEnumerable<Expression> GuessWitnesses(BoundVar x, Expression expr) {
    Contract.Requires(x != null);
    Contract.Requires(expr != null);
    var xType = x.Type.NormalizeExpand();
    if (xType is BoolType) {
      var lit = Expression.CreateBoolLiteral(x.Origin, false);
      yield return lit;
      lit = Expression.CreateBoolLiteral(x.Origin, true);
      yield return lit;
      yield break;  // there are no more possible witnesses for booleans
    } else if (xType is CharType) {
      // TODO: something could be done for character literals
    } else if (xType.IsDatatype) {
      var dt = xType.AsDatatype;
      Expression zero = Zero(x.Origin, xType);
      if (zero != null) {
        yield return zero;
      }

      foreach (var ctor in dt.Ctors) {
        if (ctor.Formals.Count == 0) {
          var v = new DatatypeValue(x.Origin, dt.Name, ctor.Name, new List<Expression>()) {
            Ctor = ctor,
            InferredTypeArgs = xType.TypeArgs,
            Type = xType
          };
          yield return v;
        }
      }
    } else if (Zero(x.Origin, xType) is { } zero) {
      yield return zero;
    }

    var bounds = ModuleResolver.DiscoverAllBounds_SingleVar(x, expr, out _);
    foreach (var bound in bounds) {
      if (bound is IntBoundedPool intBoundedPool) {
        if (intBoundedPool.LowerBound != null) {
          yield return intBoundedPool.LowerBound;
        }
        if (intBoundedPool.UpperBound != null) {
          yield return Expression.CreateDecrement(intBoundedPool.UpperBound, 1);
        }

      } else if (bound is SubSetBoundedPool subSetBoundedPool) {
        yield return subSetBoundedPool.UpperBound;

      } else if (bound is SuperSetBoundedPool superSetBoundedPool) {
        yield return superSetBoundedPool.LowerBound;

      } else if (bound is SetBoundedPool setBoundedPool) {
        if (setBoundedPool.Set.Resolved is DisplayExpression display) {
          foreach (var el in display.Elements) {
            yield return el;
          }
        }

      } else if (bound is MultiSetBoundedPool multiSetBoundedPool) {
        if (multiSetBoundedPool.MultiSet.Resolved is DisplayExpression display) {
          foreach (var el in display.Elements) {
            yield return el;
          }
        }

      } else if (bound is SeqBoundedPool seqBoundedPool) {
        if (seqBoundedPool.Seq.Resolved is DisplayExpression display) {
          foreach (var el in display.Elements) {
            yield return el;
          }
        }

      } else if (bound is MapBoundedPool mapBoundedPool) {
        if (mapBoundedPool.Map.Resolved is MapDisplayExpr display) {
          foreach (var maplet in display.Elements) {
            yield return maplet.A;
          }
        }

      } else if (bound is ExactBoundedPool exactBoundedPool) {
        yield return exactBoundedPool.E;
      }
    }
  }

  /// <summary>
  /// Return a zero-equivalent value for "typ", or return null (for any reason whatsoever).
  /// </summary>
  Expression Zero(IOrigin tok, Type typ) {
    Contract.Requires(tok != null);
    Contract.Requires(typ != null);
    typ = typ.NormalizeToAncestorType();
    if (typ is BoolType) {
      return Expression.CreateBoolLiteral(tok, false);
    } else if (typ is CharType) {
      return new CharLiteralExpr(tok, CharType.DefaultValue.ToString()) { Type = Type.Char };
    } else if (typ.IsNumericBased(Type.NumericPersuasion.Int)) {
      return Expression.CreateIntLiteral(tok, 0);
    } else if (typ.IsNumericBased(Type.NumericPersuasion.Real)) {
      return Expression.CreateRealLiteral(tok, BaseTypes.BigDec.ZERO);
    } else if (typ.IsBigOrdinalType) {
      return Expression.CreateNatLiteral(tok, 0, Type.BigOrdinal);
    } else if (typ.IsBitVectorType) {
      return new LiteralExpr(tok, 0) { Type = typ };
    } else if (typ.IsRefType) {
      return new LiteralExpr(tok) { Type = typ };  // null
    } else if (typ.IsDatatype) {
      return null;  // this can be improved
    } else if (typ is SetType setType) {
      return new SetDisplayExpr(tok, setType.Finite, []) { Type = typ };
    } else if (typ is MultiSetType) {
      return new MultiSetDisplayExpr(tok, []) { Type = typ };
    } else if (typ is SeqType) {
      return new SeqDisplayExpr(tok, []) { Type = typ };
    } else if (typ is MapType mapType) {
      return new MapDisplayExpr(tok, mapType.Finite, []) { Type = typ };
    } else if (typ is ArrowType) {
      // TODO: do better than just returning null
      return null;
    } else if (typ.IsAbstractType || typ.IsInternalTypeSynonym) {
      return null;
    } else if (typ.IsTraitType) {
      Contract.Assert(options.Get(CommonOptionBag.GeneralTraits) != CommonOptionBag.GeneralTraitsOptions.Legacy);
      return null;
    } else if (typ.IsTypeParameter) {
      return null;
    } else {
      Contract.Assume(false);  // unexpected type
      return null;
    }
  }

  void AddRevealableTypeDecl(RevealableTypeDecl d) {
    Contract.Requires(d != null);
    if (RevealedInScope(d)) {
      if (d is NewtypeDecl) {
        var dd = (NewtypeDecl)d;
        AddTypeDecl(dd);
        AddClassMembers(dd, true, true);
      } else if (d is DefaultClassDecl defaultClassDecl) {
        AddClassMembers(defaultClassDecl, options.OptimizeResolution < 1, true);
      } else if (d is ClassLikeDecl) {
        var cl = (ClassLikeDecl)d;
        AddClassMembers(cl, options.OptimizeResolution < 1, true);
        if (cl.NonNullTypeDecl != null) {
          AddTypeDecl(cl.NonNullTypeDecl);
        }
        if (d is IteratorDecl) {
          AddIteratorSpecAndBody((IteratorDecl)d);
        }
      } else if (d is DatatypeDecl) {
        var dd = (DatatypeDecl)d;
        AddDatatype(dd);
        AddClassMembers(dd, true, true);
      } else if (d is SubsetTypeDecl) {
        AddTypeDecl((SubsetTypeDecl)d);
      } else if (d is TypeSynonymDecl) {
        //do nothing, this type will be transparent to translation
      } else {
        Contract.Assert(false);
      }
    } else {
      // Create a type constructor for the export-provided type. But note:
      //   -- A DefaultClassDecl does not need a type constructor.
      //   -- Reference types give rise to two type declarations, the nullable version and the non-null version.
      //      For a type that is only export-provided, the type that is exported is an abstract-type version
      //      of the non-null type. Thus, for a class declaration and reference-type trait declaration, we
      //      do not create a type constructor.
      if (d is not DefaultClassDecl && d is not ClassLikeDecl { IsReferenceTypeDecl: true }) {
        GetOrCreateTypeConstructor(d.SelfSynonymDecl());
      }

      if (d is TopLevelDeclWithMembers topLevelDeclWithMembers) {
        AddClassMembers(topLevelDeclWithMembers, true, false);
      }
    }
  }

  void AddTypeDecl(NewtypeDecl dd) {
    Contract.Requires(dd != null);
    Contract.Ensures(fuelContext == Contract.OldValue(fuelContext));

    FuelContext oldFuelContext = this.fuelContext;
    this.fuelContext = FuelSetting.NewFuelContext(dd);

    AddWellformednessCheck(dd);

    // Add $Is and $IsAlloc axioms for the newtype
    currentModule = dd.EnclosingModuleDefinition;
    AddRedirectingTypeDeclAxioms(false, dd, dd.FullName);
    AddRedirectingTypeDeclAxioms(true, dd, dd.FullName);
    currentModule = null;

    this.fuelContext = oldFuelContext;
  }

  void AddTypeDecl(SubsetTypeDecl dd) {
    Contract.Requires(dd != null);
    Contract.Ensures(fuelContext == Contract.OldValue(fuelContext));

    FuelContext oldFuelContext = this.fuelContext;
    this.fuelContext = FuelSetting.NewFuelContext(dd);

    if (!Attributes.Contains(dd.Attributes, "axiom")) {
      AddWellformednessCheck(dd);
    }
    currentModule = dd.EnclosingModuleDefinition;
    // Add $Is and $IsAlloc axioms for the subset type
    AddRedirectingTypeDeclAxioms(false, dd, dd.FullName);
    AddRedirectingTypeDeclAxioms(true, dd, dd.FullName);
    currentModule = null;
    this.fuelContext = oldFuelContext;
  }

  /// <summary>
  /// Generate $Is (if "!generateIsAlloc") or $IsAlloc (if "generateIsAlloc") axioms for the newtype/subset-type "dd",
  /// whose printable name is "fullName".
  /// 
  /// Given that the type "dd" is
  ///
  ///     (new)type dd<X> = x: Base<Y> | constraint
  ///
  /// the $Is axioms have the form
  ///
  ///     axiom (forall o: dd ::
  ///         { $Is(o, Tclass.dd) }
  ///         $Is(o, Tclass.dd) ==>
  ///             $Is(o, Tclass.Base) && constraintCanCall && constraint);
  ///     axiom (forall o: dd ::
  ///         { $Is(o, Tclass.dd) }
  ///         $Is(o, Tclass.Base) && (constraintCanCall ==> constraint) ==>
  ///             $Is(o, Tclass.dd));
  /// 
  /// and the $IsAlloc axiom has the form
  ///
  ///     axiom (forall o: dd, $h: Heap ::
  ///         { $IsAlloc(o, Tclass.dd, $h) }
  ///         $IsAlloc(o, Tclass.dd, $h) <==> $IsAlloc(o, Tclass.Base, $h));
  /// </summary>
  void AddRedirectingTypeDeclAxioms<T>(bool generateIsAlloc, T dd, string fullName)
    where T : TopLevelDecl, RedirectingTypeDecl {
    Contract.Requires(dd != null);
    Contract.Requires((dd.Var != null && dd.Constraint != null) || dd is NewtypeDecl);
    Contract.Requires(fullName != null);

    var vars = MkTyParamBinders(dd.TypeArgs, out var typeArgs);
    var typeTerm = ClassTyCon(dd, typeArgs);

    var baseType = dd.Var != null ? dd.Var.Type : ((NewtypeDecl)(object)dd).BaseType;
    var oBplType = TrType(baseType);
    var c = new BoundVar(dd.Origin, CurrentIdGenerator.FreshId("c"), baseType);
    var o = BplBoundVar((dd.Var ?? c).AssignUniqueName((dd.IdGenerator)), oBplType, vars);

    if (generateIsAlloc) {
      var h = BplBoundVar("$h", Predef.HeapType, vars);
      // $IsAlloc(o, ..)
      var isAlloc = MkIsAlloc(o, typeTerm, h, ModeledAsBoxType(baseType));
      Bpl.Expr body;
      var trigger = BplTrigger(isAlloc);
      if (baseType.IsNumericBased() || baseType.IsBitVectorType || baseType.IsBoolType || baseType.IsCharType) {
        body = isAlloc;
      } else {
        Bpl.Expr rhs = MkIsAlloc(o, baseType, h);
        if (dd is NonNullTypeDecl) {
          trigger.Next = BplTrigger(rhs);
        }
        body = BplIff(isAlloc, rhs);
      }

      var comment = $"$IsAlloc axiom for {dd.WhatKind} {fullName}";
      var axiom = new Bpl.Axiom(dd.Tok, BplForall(vars, BplTrigger(isAlloc), body), comment);
      AddOtherDefinition(GetOrCreateTypeConstructor(dd), axiom);

    } else {
      // $Is(o, ..)
      var isPredicate = MkIs(o, typeTerm, ModeledAsBoxType(baseType));
      var trigger = BplTrigger(isPredicate);
      var etran = new ExpressionTranslator(this, Predef, NewOneHeapExpr(dd.Origin), null);
      Bpl.Expr parentConstraint;
      Expression condition;
      if (baseType.IsNumericBased() || baseType.IsBitVectorType || baseType.IsBoolType || baseType.IsCharType) {
        // optimize this to only use the numeric/bitvector constraint, not the whole $Is thing on the base type
        parentConstraint = Bpl.Expr.True;
        var udt = UserDefinedType.FromTopLevelDecl(dd.Origin, dd);
        var idExpr = Expression.CreateIdentExpr(dd.Var ?? c);
        condition = ModuleResolver.GetImpliedTypeConstraint(idExpr, udt);
      } else {
        parentConstraint = MkIs(o, baseType);
        if (dd is NonNullTypeDecl) {
          trigger.Next = BplTrigger(parentConstraint);
        }
        condition = dd.Constraint ?? Expression.CreateBoolLiteral(dd.Origin, true);
      }

      var constraintCanCall = etran.CanCallAssumption(condition);
      if (ArrowType.IsPartialArrowTypeName(dd.Name)) {
        // Hack for now. TODO: The resolver currently sets up the constraint of a partial arrow as being
        // a total arrow such that "forall bx: Box :: f(bx) == {}". However, it ought to be
        // "forall bx: Box :: f.requires(bx) ==> f(bx) == {}". When that gets fixed, the hack here is no longer needed.
        constraintCanCall = Bpl.Expr.True;
      }
      var canCallIsJustTrue = constraintCanCall == Bpl.Expr.True;
      var constraint = etran.TrExpr(condition);
      var comment = $"$Is axiom{(canCallIsJustTrue ? "" : "s")} for {dd.WhatKind} {fullName}";

      var rhs = BplAnd(parentConstraint, BplAnd(constraintCanCall, constraint));
      var body = canCallIsJustTrue ? BplIff(isPredicate, rhs) : BplImp(isPredicate, rhs);
      var axiom = new Bpl.Axiom(dd.Origin, BplForall(vars, trigger, body), comment);
      AddOtherDefinition(GetOrCreateTypeConstructor(dd), axiom);

      if (!canCallIsJustTrue) {
        body = BplImp(BplAnd(parentConstraint, BplImp(constraintCanCall, constraint)), isPredicate);
        axiom = new Bpl.Axiom(dd.Origin, BplForall(vars, BplTrigger(isPredicate), body), null);
        AddOtherDefinition(GetOrCreateTypeConstructor(dd), axiom);
      }
    }
  }


  /// <summary>
  /// Returns the translation of converting "r", whose Dafny type was "fromType", to a value of type "toType".
  /// The translation assumes that "r" is known to be a value of type "toType".
  /// </summary>
  Bpl.Expr ConvertExpression(IOrigin tok, Bpl.Expr r, Type fromType, Type toType) {
    Contract.Requires(tok != null);
    Contract.Requires(r != null);
    Contract.Requires(fromType != null);
    Contract.Requires(toType != null);
    toType = toType.NormalizeToAncestorType();
    fromType = fromType.NormalizeToAncestorType();
    if (fromType.IsTypeParameter) {
      return UnboxUnlessInherentlyBoxed(r, toType);
    } else if (fromType.IsNumericBased(Type.NumericPersuasion.Int)) {
      if (toType.IsNumericBased(Type.NumericPersuasion.Int)) {
        // do nothing
      } else if (toType.IsNumericBased(Type.NumericPersuasion.Real)) {
        r = FunctionCall(tok, BuiltinFunction.IntToReal, null, r);
      } else if (toType.IsCharType) {
        r = FunctionCall(tok, BuiltinFunction.CharFromInt, null, r);
      } else if (toType.IsBitVectorType) {
        r = IntToBV(tok, r, toType);
      } else if (toType.IsBigOrdinalType) {
        r = FunctionCall(tok, "ORD#FromNat", Predef.BigOrdinalType, r);
      } else {
        Contract.Assert(false, $"No translation implemented from {fromType} to {toType}");
      }
      return r;
    } else if (fromType.IsBitVectorType) {
      var fromWidth = fromType.AsBitVectorType.Width;
      if (toType.IsBitVectorType) {
        // conversion from one bitvector type to another
        var toWidth = toType.AsBitVectorType.Width;
        if (fromWidth == toWidth) {
          // no conversion
        } else if (fromWidth < toWidth) {
          var zeros = BplBvLiteralExpr(tok, BaseTypes.BigNum.ZERO, toWidth - fromWidth);
          if (fromWidth == 0) {
            r = zeros;
          } else {
            var concat = new Bpl.BvConcatExpr(tok, zeros, r);
            // There's a bug in Boogie that causes a warning to be emitted if a BvConcatExpr is passed as the argument
            // to $Box, which takes a type argument.  The bug can apparently be worked around by giving an explicit
            // (and other redudant) type conversion.
            r = Bpl.Expr.CoerceType(tok, concat, BplBvType(toWidth));
          }
        } else if (toWidth == 0) {
          r = BplBvLiteralExpr(tok, BaseTypes.BigNum.ZERO, toWidth);
        } else {
          r = new Bpl.BvExtractExpr(tok, r, toWidth, 0);
        }
      } else if (toType.IsNumericBased(Type.NumericPersuasion.Int)) {
        r = FunctionCall(tok, "nat_from_bv" + fromWidth, Bpl.Type.Int, r);
      } else if (toType.IsNumericBased(Type.NumericPersuasion.Real)) {
        r = FunctionCall(tok, "nat_from_bv" + fromWidth, Bpl.Type.Int, r);
        r = FunctionCall(tok, BuiltinFunction.IntToReal, null, r);
      } else if (toType.IsCharType) {
        r = FunctionCall(tok, "nat_from_bv" + fromWidth, Bpl.Type.Int, r);
        r = FunctionCall(tok, BuiltinFunction.CharFromInt, null, r);
      } else if (toType.IsBigOrdinalType) {
        r = FunctionCall(tok, "nat_from_bv" + fromWidth, Bpl.Type.Int, r);
        r = FunctionCall(tok, "ORD#FromNat", Predef.BigOrdinalType, r);
      } else {
        Contract.Assert(false, $"No translation implemented from {fromType} to {toType}");
      }
      return r;
    } else if (fromType.IsCharType) {
      if (toType.IsNumericBased(Type.NumericPersuasion.Int)) {
        r = FunctionCall(tok, BuiltinFunction.CharToInt, null, r);
      } else if (toType.IsCharType) {
        // do nothing
      } else if (toType.IsNumericBased(Type.NumericPersuasion.Real)) {
        r = FunctionCall(tok, BuiltinFunction.CharToInt, null, r);
        r = FunctionCall(tok, BuiltinFunction.IntToReal, null, r);
      } else if (toType.IsBitVectorType) {
        r = FunctionCall(tok, BuiltinFunction.CharToInt, null, r);
        r = IntToBV(tok, r, toType);
      } else if (toType.IsBigOrdinalType) {
        r = FunctionCall(tok, BuiltinFunction.CharToInt, null, r);
        r = FunctionCall(tok, "ORD#FromNat", Bpl.Type.Int, r);
      } else {
        Contract.Assert(false, $"No translation implemented from {fromType} to {toType}");
      }
      return r;
    } else if (fromType.IsNumericBased(Type.NumericPersuasion.Real)) {
      if (toType.IsNumericBased(Type.NumericPersuasion.Real)) {
        // do nothing
      } else if (toType.IsNumericBased(Type.NumericPersuasion.Int)) {
        r = FunctionCall(tok, BuiltinFunction.RealToInt, null, r);
      } else if (toType.IsBitVectorType) {
        r = FunctionCall(tok, BuiltinFunction.RealToInt, null, r);
        r = IntToBV(tok, r, toType);
      } else if (toType.IsCharType) {
        r = FunctionCall(tok, BuiltinFunction.RealToInt, null, r);
        r = FunctionCall(tok, BuiltinFunction.CharFromInt, null, r);
      } else if (toType.IsBigOrdinalType) {
        r = FunctionCall(tok, BuiltinFunction.RealToInt, null, r);
        r = FunctionCall(tok, "ORD#FromNat", Bpl.Type.Int, r);
      } else {
        Contract.Assert(false, $"No translation implemented from {fromType} to {toType}");
      }
      return r;
      // "r" now denotes an integer
    } else if (fromType.IsBigOrdinalType) {
      if (toType.IsNumericBased(Type.NumericPersuasion.Int)) {
        r = FunctionCall(tok, "ORD#Offset", Bpl.Type.Int, r);
      } else if (toType.IsNumericBased(Type.NumericPersuasion.Real)) {
        r = FunctionCall(tok, "ORD#Offset", Bpl.Type.Int, r);
        r = FunctionCall(tok, BuiltinFunction.IntToReal, null, r);
      } else if (toType.IsCharType) {
        r = FunctionCall(tok, "ORD#Offset", Bpl.Type.Int, r);
        r = FunctionCall(tok, BuiltinFunction.CharFromInt, null, r);
      } else if (toType.IsBitVectorType) {
        r = FunctionCall(tok, "ORD#Offset", Bpl.Type.Int, r);
        r = IntToBV(tok, r, toType);
      } else if (toType.IsBigOrdinalType) {
        // do nothing
      } else {
        Contract.Assert(false, $"No translation implemented from {fromType} to {toType}");
      }
      return r;
    } else if (fromType.IsRefType && toType.IsRefType) {
      return r;
    } else if (fromType.IsRefType) {
      Contract.Assert(toType.IsTraitType);
      return BoxIfNecessary(r.tok, r, fromType);
    } else if (toType.IsRefType) {
      Contract.Assert(fromType.IsTraitType);
      return UnboxUnlessInherentlyBoxed(r, toType);
    } else if (toType.IsTraitType) {
      // cast to a non-reference trait
      return BoxIfNecessary(r.tok, r, fromType);
    } else if (fromType.IsTraitType) {
      // cast from a non-reference trait
      return UnboxUnlessInherentlyBoxed(r, toType);
    } else if (fromType.IsSubtypeOf(toType, false, false)) {
      return AdaptBoxing(r.tok, r, fromType, toType);
    } else {
      // In all other legal cases, the representations of "fromType" and "toType" are the same.
      // The following assertion shows which cases we expect.
      Contract.Assert(
        Type.SameHead(fromType, toType) ||
        fromType.AsNewtype != null ||
        toType.AsNewtype != null
      );
      return r;
    }
  }

  private Bpl.Expr IntToBV(IOrigin tok, Bpl.Expr r, Type toType) {
    var toWidth = toType.AsBitVectorType.Width;
    if (RemoveLit(r) is Bpl.LiteralExpr) {
      Bpl.LiteralExpr e = (Bpl.LiteralExpr)RemoveLit(r);
      if (e.isBigNum) {
        var toBound = BaseTypes.BigNum.FromBigInt(BigInteger.One << toWidth);  // 1 << toWidth
        if (e.asBigNum <= toBound) {
          return BplBvLiteralExpr(r.tok, e.asBigNum, toType.AsBitVectorType);
        }
      }
    }
    return FunctionCall(tok, "nat_to_bv" + toWidth, BplBvType(toWidth), r);
  }

  /// <summary>
  /// Emit checks that "expr" (which may or may not be a value of type "expr.Type"!) is a value of type "toType".
  /// </summary>
  void CheckResultToBeInType(IOrigin tok, Expression expr, Type toType, Variables locals, BoogieStmtListBuilder builder, ExpressionTranslator etran, string errorMsgPrefix = "") {
    Contract.Requires(tok != null);
    Contract.Requires(expr != null);
    Contract.Requires(toType != null);
    Contract.Requires(builder != null);
    Contract.Requires(etran != null);
    Contract.Requires(errorMsgPrefix != null);

    var toTypeFamily = toType.NormalizeToAncestorType();
    var fromType = expr.Type;
    var fromTypeFamily = expr.Type.NormalizeToAncestorType();

    // Lazily create a local variable "o" to hold the value of the from-expression
    Bpl.IdentifierExpr o = null;
    void PutSourceIntoLocal() {
      if (o == null) {
        var oType = fromType.IsCharType ? Type.Int : fromType;
        var oVar = locals.GetOrAdd(new Bpl.LocalVariable(tok, new Bpl.TypedIdent(tok, CurrentIdGenerator.FreshId("newtype$check#"), TrType(oType))));
        o = new Bpl.IdentifierExpr(tok, oVar);
        var rhs = etran.TrExpr(expr);
        if (fromType.IsCharType) {
          rhs = FunctionCall(expr.Origin, "char#ToInt", Bpl.Type.Int, rhs);
        }
        builder.Add(Bpl.Cmd.SimpleAssign(tok, o, rhs));
      }
    }

    Contract.Assert(options.Get(CommonOptionBag.GeneralTraits) != CommonOptionBag.GeneralTraitsOptions.Legacy ||
                    fromType.IsRefType == toType.IsRefType ||
                    (fromType.IsTypeParameter && toType.IsTraitType));
    if (toType.IsRefType || fromType.IsTraitType || toType.IsArrowType) {
      PutSourceIntoLocal();
      CheckSubrange(tok, o, fromType, toType, expr, builder, errorMsgPrefix);
      return;
    }

    if (fromType.IsNumericBased(Type.NumericPersuasion.Real) && !toType.IsNumericBased(Type.NumericPersuasion.Real)) {
      // this operation is well-formed only if the real-based number represents an integer
      //   assert Real(Int(o)) == o;
      PutSourceIntoLocal();
      Bpl.Expr from = FunctionCall(tok, BuiltinFunction.RealToInt, null, o);
      Bpl.Expr e = FunctionCall(tok, BuiltinFunction.IntToReal, null, from);
      e = Bpl.Expr.Binary(tok, Bpl.BinaryOperator.Opcode.Eq, e, o);
      builder.Add(Assert(tok, e, new IsInteger(expr, errorMsgPrefix), builder.Context));
    }

    if (fromType.IsBigOrdinalType && !toType.IsBigOrdinalType) {
      PutSourceIntoLocal();
      Bpl.Expr boundsCheck = FunctionCall(tok, "ORD#IsNat", Bpl.Type.Bool, o);
      builder.Add(Assert(tok, boundsCheck, new ConversionIsNatural(errorMsgPrefix, expr), builder.Context));
    }

    if (toTypeFamily.IsBitVectorType) {
      var toWidth = toTypeFamily.AsBitVectorType.Width;
      var toBound = BaseTypes.BigNum.FromBigInt(BigInteger.One << toWidth);  // 1 << toWidth
      Bpl.Expr boundsCheck = null;
      var dafnyBound = new BinaryExpr(expr.Origin, BinaryExpr.Opcode.LeftShift, Expression.CreateIntLiteral(expr.Origin, 1), Expression.CreateIntLiteral(expr.Origin, toWidth));
      Expression dafnyBoundsCheck = null;
      if (fromTypeFamily.IsBitVectorType) {
        var fromWidth = fromTypeFamily.AsBitVectorType.Width;
        if (toWidth < fromWidth) {
          // Check "expr < (1 << toWidth)" in type "fromType" (note that "1 << toWidth" is indeed a value in "fromType")
          PutSourceIntoLocal();
          var bound = BplBvLiteralExpr(tok, toBound, fromTypeFamily.AsBitVectorType);
          boundsCheck = FunctionCall(expr.Origin, "lt_bv" + fromWidth, Bpl.Type.Bool, o, bound);
          dafnyBoundsCheck = new BinaryExpr(expr.Origin, BinaryExpr.Opcode.And,
            new BinaryExpr(expr.Origin, BinaryExpr.Opcode.Le, new LiteralExpr(expr.Origin, 0), expr),
            new BinaryExpr(expr.Origin, BinaryExpr.Opcode.Lt, expr, dafnyBound)
        );
        }
      } else if (fromType.IsNumericBased(Type.NumericPersuasion.Int) || fromTypeFamily.IsCharType) {
        // Check "expr < (1 << toWidth)" in type "int"
        PutSourceIntoLocal();
        var bound = Bpl.Expr.Literal(toBound);
        boundsCheck = BplAnd(Bpl.Expr.Le(Bpl.Expr.Literal(0), o), Bpl.Expr.Lt(o, bound));
        dafnyBoundsCheck = Expression.CreateAnd(
          Expression.CreateLess(Expression.CreateIntLiteral(expr.Origin, 0), expr),
          Expression.CreateAtMost(expr, dafnyBound));
      } else if (fromType.IsNumericBased(Type.NumericPersuasion.Real)) {
        // Check "Int(expr) < (1 << toWidth)" in type "int"
        PutSourceIntoLocal();
        var bound = Bpl.Expr.Literal(toBound);
        var oi = FunctionCall(tok, BuiltinFunction.RealToInt, null, o);
        boundsCheck = BplAnd(Bpl.Expr.Le(Bpl.Expr.Literal(0), oi), Bpl.Expr.Lt(oi, bound));
        var intExpr = new ExprDotName(expr.Origin, expr, new Name("Floor"), null);
        dafnyBoundsCheck = new BinaryExpr(expr.Origin, BinaryExpr.Opcode.And,
          new BinaryExpr(expr.Origin, BinaryExpr.Opcode.Le, new LiteralExpr(expr.Origin, 0), intExpr),
          new BinaryExpr(expr.Origin, BinaryExpr.Opcode.Lt, intExpr, dafnyBound)
        );
      } else if (fromType.IsBigOrdinalType) {
        var bound = Bpl.Expr.Literal(toBound);
        var oi = FunctionCall(tok, "ORD#Offset", Bpl.Type.Int, o);
        boundsCheck = Bpl.Expr.Lt(oi, bound);
        var intExpr = new ExprDotName(expr.Origin, expr, new Name("Offset"), null);
        dafnyBoundsCheck = new BinaryExpr(expr.Origin, BinaryExpr.Opcode.And,
          new BinaryExpr(expr.Origin, BinaryExpr.Opcode.Le, new LiteralExpr(expr.Origin, 0), intExpr),
          new BinaryExpr(expr.Origin, BinaryExpr.Opcode.Lt, intExpr, dafnyBound)
        );
      }

      if (boundsCheck != null) {
        builder.Add(Assert(tok, boundsCheck, new ConversionFit("value", toType, dafnyBoundsCheck, errorMsgPrefix), builder.Context));
      }

    } else if (toType.IsCharType) {
      if (fromType.IsNumericBased(Type.NumericPersuasion.Int)) {
        PutSourceIntoLocal();
        var boundsCheck = FunctionCall(Token.NoToken, BuiltinFunction.IsChar, null, o);
        var dafnyBoundsCheck = Utils.MakeCharBoundsCheck(options, expr);
        builder.Add(Assert(tok, boundsCheck, new ConversionFit("value", toType, dafnyBoundsCheck, errorMsgPrefix), builder.Context));
      } else if (fromType.IsNumericBased(Type.NumericPersuasion.Real)) {
        PutSourceIntoLocal();
        var oi = FunctionCall(tok, BuiltinFunction.RealToInt, null, o);
        var boundsCheck = FunctionCall(Token.NoToken, BuiltinFunction.IsChar, null, oi);
        Expression intExpr = new ExprDotName(expr.Origin, expr, new Name("Floor"), null);
        var dafnyBoundsCheck = Utils.MakeCharBoundsCheck(options, intExpr);
        builder.Add(Assert(tok, boundsCheck, new ConversionFit("real value", toType, dafnyBoundsCheck, errorMsgPrefix), builder.Context));
      } else if (fromType.IsBitVectorType) {
        PutSourceIntoLocal();
        var fromWidth = fromType.AsBitVectorType.Width;
        var toWidth = 16;
        if (toWidth < fromWidth) {
          // Check "expr < (1 << toWidth)" in type "fromType" (note that "1 << toWidth" is indeed a value in "fromType")
          PutSourceIntoLocal();
          var toBound = BaseTypes.BigNum.FromBigInt(BigInteger.One << toWidth); // 1 << toWidth
          var bound = BplBvLiteralExpr(tok, toBound, fromType.AsBitVectorType);
          var boundsCheck = FunctionCall(expr.Origin, "lt_bv" + fromWidth, Bpl.Type.Bool, o, bound);
          var dafnyBound = new BinaryExpr(expr.Origin, BinaryExpr.Opcode.LeftShift, Expression.CreateIntLiteral(expr.Origin, 1), Expression.CreateIntLiteral(expr.Origin, toWidth));
          var dafnyBoundsCheck = new BinaryExpr(expr.Origin, BinaryExpr.Opcode.Lt, expr, dafnyBound);
          builder.Add(Assert(tok, boundsCheck, new ConversionFit("bit-vector value", toType, dafnyBoundsCheck, errorMsgPrefix), builder.Context));
        }
      } else if (fromType.IsBigOrdinalType) {
        PutSourceIntoLocal();
        var oi = FunctionCall(tok, "ORD#Offset", Bpl.Type.Int, o);
        int toWidth = 16;
        var toBound = BaseTypes.BigNum.FromBigInt(BigInteger.One << toWidth); // 1 << toWidth
        var bound = Bpl.Expr.Literal(toBound);
        var boundsCheck = Bpl.Expr.Lt(oi, bound);
        var dafnyBound = new BinaryExpr(expr.Origin, BinaryExpr.Opcode.LeftShift, Expression.CreateIntLiteral(expr.Origin, 1), Expression.CreateIntLiteral(expr.Origin, toWidth));
        var offset = new ExprDotName(expr.Origin, expr, new Name("Offset"), null);
        var dafnyBoundsCheck = new BinaryExpr(expr.Origin, BinaryExpr.Opcode.Lt, offset, dafnyBound);
        builder.Add(Assert(tok, boundsCheck, new ConversionFit("ORDINAL value", toType, dafnyBoundsCheck, errorMsgPrefix), builder.Context));
      }

    } else if (toType.IsBigOrdinalType) {
      if (fromType.IsNumericBased(Type.NumericPersuasion.Int)) {
        PutSourceIntoLocal();
        Bpl.Expr boundsCheck = Bpl.Expr.Le(Bpl.Expr.Literal(0), o);
        var desc = new ConversionPositive("integer", toType, expr, errorMsgPrefix);
        builder.Add(Assert(tok, boundsCheck, desc, builder.Context));
      }
      if (fromType.IsNumericBased(Type.NumericPersuasion.Real)) {
        PutSourceIntoLocal();
        var oi = FunctionCall(tok, BuiltinFunction.RealToInt, null, o);
        Bpl.Expr boundsCheck = Bpl.Expr.Le(Bpl.Expr.Literal(0), oi);
        var intExpr = new ExprDotName(expr.Origin, expr, new Name("Floor"), null);
        var desc = new ConversionPositive("real", toType, intExpr, errorMsgPrefix);
        builder.Add(Assert(tok, boundsCheck, desc, builder.Context));
      }

    } else if (toType.IsNumericBased(Type.NumericPersuasion.Int)) {
      // already checked that BigOrdinal or real inputs are integral
    } else if (toType.IsNumericBased(Type.NumericPersuasion.Real)) {
      // already checked that BigOrdinal is integral
    }

    if (toType.NormalizeExpandKeepConstraints().AsRedirectingType != null) {
      PutSourceIntoLocal();
      Bpl.Expr be;
      if (fromType.IsNumericBased() || fromTypeFamily.IsBitVectorType) {
        be = ConvertExpression(expr.Origin, o, fromType, toType);
      } else if (fromType.IsCharType) {
        be = ConvertExpression(expr.Origin, o, Dafny.Type.Int, toType);
      } else if (fromType.IsBigOrdinalType) {
        be = FunctionCall(expr.Origin, "ORD#Offset", Bpl.Type.Int, o);
        be = ConvertExpression(expr.Origin, be, Dafny.Type.Int, toType);
      } else {
        be = o;
      }
      CheckResultToBeInType_Aux(tok, new BoogieWrapper(be, toTypeFamily), expr, toType.NormalizeExpandKeepConstraints(), builder, etran, errorMsgPrefix);
    }
  }

  void CheckResultToBeInType_Aux(IOrigin tok, Expression boogieExpr, Expression origExpr, Type toType, BoogieStmtListBuilder builder, ExpressionTranslator etran, string errorMsgPrefix) {
    Contract.Requires(tok != null);
    Contract.Requires(boogieExpr != null);
    Contract.Requires(origExpr != null);
    Contract.Requires(toType != null && toType.AsRedirectingType != null);
    Contract.Requires(builder != null);
    Contract.Requires(etran != null);
    Contract.Requires(errorMsgPrefix != null);
    // First, check constraints of base types
    var udt = (UserDefinedType)toType;
    var rdt = (RedirectingTypeDecl)udt.ResolvedClass;
    Type baseType;
    string kind;
    if (rdt is SubsetTypeDecl) {
      baseType = ((SubsetTypeDecl)rdt).RhsWithArgument(udt.TypeArgs);
      kind = "subset type";
    } else if (rdt is NewtypeDecl) {
      baseType = ((NewtypeDecl)rdt).BaseType;
      kind = "newtype";
    } else {
      baseType = ((TypeSynonymDecl)rdt).RhsWithArgument(udt.TypeArgs);
      kind = "type synonym";
    }

    if (baseType.AsRedirectingType != null) {
      CheckResultToBeInType_Aux(tok, boogieExpr, origExpr, baseType, builder, etran, errorMsgPrefix);
    }
    // Check any constraint defined in 'dd'
    if (rdt.Var != null) {
      // TODO: use TrSplitExpr
      var typeMap = TypeParameter.SubstitutionMap(rdt.TypeArgs, udt.TypeArgs);
      var dafnyConstraint = Substitute(rdt.Constraint, null, new() { { rdt.Var, origExpr } }, typeMap);
      var boogieConstraint = Substitute(rdt.Constraint, null, new() { { rdt.Var, boogieExpr } }, typeMap);

      var canCall = etran.CanCallAssumption(boogieConstraint);
      var constraint = etran.TrExpr(boogieConstraint);
      builder.Add(Assert(tok, BplImp(canCall, constraint), new ConversionSatisfiesConstraints(errorMsgPrefix, kind, rdt.Name, dafnyConstraint), builder.Context));
    }
  }


  void AddWellformednessCheck(RedirectingTypeDecl decl) {
    Contract.Requires(decl != null);
    Contract.Requires(sink != null && Predef != null);
    Contract.Requires(currentModule == null && codeContext == null && IsAllocContext == null);
    Contract.Ensures(currentModule == null && codeContext == null && IsAllocContext == null);

    proofDependencies.SetCurrentDefinition(MethodVerboseName(decl.FullDafnyName, MethodTranslationKind.SpecWellformedness), null);

    if (!InVerificationScope(decl)) {
      // Checked in other file
      return;
    }

    currentModule = decl.Module;
    codeContext = new CallableWrapper(decl, true);
    var etran = new ExpressionTranslator(this, Predef, decl.Tok, null);

    // parameters of the procedure
    var inParams = MkTyParamFormals(decl.TypeArgs, true);
    Type baseType;
    Bpl.Expr whereClause;
    if (decl.Var != null) {
      baseType = decl.Var.Type;
      Bpl.Type varType = TrType(baseType);
      whereClause = GetWhereClause(decl.Var.Origin, new Bpl.IdentifierExpr(decl.Var.Origin, decl.Var.AssignUniqueName(decl.IdGenerator), varType), baseType, etran, NOALLOC);
      // Do NOT use a where-clause in this declaration, because that would spoil the witness checking.
      inParams.Add(new Bpl.Formal(decl.Var.Origin, new Bpl.TypedIdent(decl.Var.Origin, decl.Var.AssignUniqueName(decl.IdGenerator), varType), true));
    } else {
      baseType = ((NewtypeDecl)decl).BaseType;
      whereClause = null;
    }

    // the procedure itself
    var req = new List<Bpl.Requires>();
    // modifies $Heap
    var mod = new List<Bpl.IdentifierExpr> {
        etran.HeapCastToIdentifierExpr,
      };
    var name = MethodName(decl, MethodTranslationKind.SpecWellformedness);
    var proc = new Bpl.Procedure(decl.Tok, name, [],
      inParams, [],
      false, req, mod, [], etran.TrAttributes(decl.Attributes, null));
    AddVerboseNameAttribute(proc, decl.FullDafnyName, MethodTranslationKind.SpecWellformedness);
    sink.AddTopLevelDeclaration(proc);

    // TODO: Can a checksum be inserted here?

    Contract.Assert(proc.InParams.Count == inParams.Count);
    // Changed the next line to strip from inParams instead of proc.InParams
    // They should be the same, but hence the added contract
    var implInParams = Bpl.Formal.StripWhereClauses(inParams);
    var locals = new Variables();
    var context = new BodyTranslationContext(false);
    var builder = new BoogieStmtListBuilder(this, options, context);
    builder.Add(new CommentCmd(string.Format("AddWellformednessCheck for {0} {1}", decl.WhatKind, decl)));
    builder.AddCaptureState(decl.Tok, false, "initial state");
    IsAllocContext = new IsAllocContext(options, true);

    DefineFrame(decl.Tok, etran.ReadsFrame(decl.Tok), [], builder, locals, null);

    // some initialization stuff;  // This is collected in builderInitializationArea
    // define frame;
    // if (*) {
    //   // The following is collected in constraintCheckBuilder:
    //   assume the where-clause for the bound variable
    //   check constraint is well-formed;
    //   assume constraint;
    //   do reads checks;
    // } else {
    //   // The following is collected in witnessCheckBuilder:
    //   check witness;
    // }

    // check well-formedness of the constraint (including termination, and delayed reads checks)
    var builderInitializationArea = CheckConstraintWellformedness(decl, context, whereClause, etran, locals, builder);

    // Check that the type is inhabited.
    // Note, the possible witness in this check should be coordinated with the compiler, so the compiler knows how to do the initialization
    Expression witnessExpr = null;
    var witnessCheckBuilder = new BoogieStmtListBuilder(this, options, context);
    witnessCheckBuilder.Add(new Bpl.CommentCmd($"check well-formedness of {decl.WhatKind} witness, and that it satisfies the constraint"));
    string witnessString = null;
    if (decl.Witness != null) {
      // check well-formedness of the witness expression (including termination, and reads checks)
      var ghostCodeContext = codeContext;
      codeContext = decl.WitnessKind == SubsetTypeDecl.WKind.Compiled ? new CallableWrapper(decl, false) : ghostCodeContext;
      CheckWellformedWithResult(decl.Witness, new WFOptions(null, true), locals, witnessCheckBuilder, etran,
        (returnBuilder, result) => {
          // check that the witness is assignable to the type of the given bound variable
          if (decl is SubsetTypeDecl) {
            // Note, for new-types, this has already been checked by CheckWellformed.
            CheckResultToBeInType(result.Origin, result, decl.Var.Type, locals, returnBuilder, etran);
          }

          // check that the witness is assignable to the type of the given bound variable
          CheckResultToBeInType(decl.Witness.Origin, decl.Witness, baseType, locals, witnessCheckBuilder, etran);
          // check that the witness expression checks out
          witnessExpr = decl.Constraint != null ? Substitute(decl.Constraint, decl.Var, decl.Witness) : null;
          if (witnessExpr != null) {
            witnessExpr.SetOrigin(result.Origin);
            var desc = new WitnessCheck(witnessString, witnessExpr);
            SplitAndAssertExpression(returnBuilder, witnessExpr, etran, context, desc);
          }
        });
      codeContext = ghostCodeContext;
    } else if (decl.WitnessKind == SubsetTypeDecl.WKind.CompiledZero) {
      var witness = Zero(decl.Tok, baseType);
      if (witness == null) {
        witnessString = "";
        witnessCheckBuilder.Add(Assert(decl.Tok, Bpl.Expr.False, new WitnessCheck(witnessString), builder.Context));
      } else {
        // before trying 0 as a witness, check that 0 can be assigned to baseType
        witnessString = Printer.ExprToString(options, witness);
        CheckResultToBeInType(decl.Tok, witness, baseType, locals, witnessCheckBuilder, etran, $"trying witness {witnessString}: ");
        witnessExpr = decl.Constraint != null ? Substitute(decl.Constraint, decl.Var, witness) : null;
        if (witnessExpr != null) {
          witnessExpr.SetOrigin(decl.Tok);
          var desc = new WitnessCheck(witnessString, witnessExpr);
          SplitAndAssertExpression(witnessCheckBuilder, witnessExpr, etran, context, desc);
        }
      }
    }
    PathAsideBlock(decl.Origin, witnessCheckBuilder, builder);

    var s0 = builderInitializationArea.Collect(decl.Tok);
    var s1 = builder.Collect(decl.Tok);
    var implBody = new StmtList(new List<BigBlock>(s0.BigBlocks.Concat(s1.BigBlocks)), decl.Tok);

    if (EmitImplementation(decl.Attributes)) {
      // emit the impl only when there are proof obligations.
      QKeyValue kv = etran.TrAttributes(decl.Attributes, null);

      AddImplementationWithAttributes(GetToken(decl), proc, implInParams, [], locals, implBody, kv);
    }

    // TODO: Should a checksum be inserted here?

    Contract.Assert(currentModule == decl.Module);
    Contract.Assert(CodeContextWrapper.Unwrap(codeContext) == decl);
    IsAllocContext = null;
    Reset();
  }

  private void SplitAndAssertExpression(BoogieStmtListBuilder witnessCheckBuilder, Expression witnessExpr,
    ExpressionTranslator etran, BodyTranslationContext context, WitnessCheck desc) {
    witnessCheckBuilder.Add(new Bpl.AssumeCmd(witnessExpr.Origin, etran.CanCallAssumption(witnessExpr)));

    var ss = TrSplitExpr(context, witnessExpr, etran, true, out var splitHappened);
    if (!splitHappened) {
      witnessCheckBuilder.Add(Assert(witnessExpr.Origin, etran.TrExpr(witnessExpr), desc, context));
    } else {
      foreach (var split in ss) {
        if (split.IsChecked) {
          var tok = witnessExpr.Origin is { } t
            ? new NestedOrigin(t, split.Tok, "this proposition could not be proved")
            : witnessExpr.Origin;
          witnessCheckBuilder.Add(AssertAndForget(witnessCheckBuilder.Context, tok, split.E, desc));
        }
      }
    }
  }

  private BoogieStmtListBuilder CheckConstraintWellformedness(RedirectingTypeDecl decl, BodyTranslationContext context,
    Bpl.Expr whereClause, ExpressionTranslator etran, Variables locals, BoogieStmtListBuilder builder) {
    var constraintCheckBuilder = new BoogieStmtListBuilder(this, options, context);
    var builderInitializationArea = new BoogieStmtListBuilder(this, options, context);
    if (decl.Constraint == null) {
      constraintCheckBuilder.Add(new Bpl.CommentCmd($"well-formedness of {decl.WhatKind} constraint is trivial"));
    } else {
      constraintCheckBuilder.Add(new Bpl.CommentCmd($"check well-formedness of {decl.WhatKind} constraint"));
      if (whereClause != null) {
        constraintCheckBuilder.Add(new Bpl.AssumeCmd(decl.Tok, whereClause));
      }
      var delayer = new ReadsCheckDelayer(etran, null, locals, builderInitializationArea, constraintCheckBuilder);
      delayer.DoWithDelayedReadsChecks(false, wfo => {
        CheckWellformedAndAssume(decl.Constraint, wfo, locals, constraintCheckBuilder, etran, "predicate subtype constraint");
      });
    }

    PathAsideBlock(decl.Origin, constraintCheckBuilder, builder);
    return builderInitializationArea;
  }
}
