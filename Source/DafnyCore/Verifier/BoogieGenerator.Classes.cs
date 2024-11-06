//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Numerics;
using System.Diagnostics.Contracts;
using Bpl = Microsoft.Boogie;
using BplParser = Microsoft.Boogie.Parser;
using System.Text;
using System.Threading;
using DafnyCore;
using Microsoft.Boogie;
using static Microsoft.Dafny.Util;
using DafnyCore.Verifier;
using JetBrains.Annotations;
using Microsoft.Dafny.Triggers;
using PODesc = Microsoft.Dafny.ProofObligationDescription;
using static Microsoft.Dafny.GenericErrors;

namespace Microsoft.Dafny;

public partial class BoogieGenerator {
  

    // This one says that this is /directly/ allocated, not that its "children" are,
    // i.e. h[x, alloc]
    public Bpl.Expr IsAlloced(IToken tok, Bpl.Expr heapExpr, Bpl.Expr e) {
      Contract.Requires(tok != null);
      Contract.Requires(heapExpr != null);
      Contract.Requires(e != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      return ApplyUnbox(tok, ReadHeap(tok, heapExpr, e, Predef.Alloc(tok)), Bpl.Type.Bool);
    }

    /// <summary>
    /// Returns read(heap: Heap, r: ref, f: Field) : Box.
    /// </summary>
    public Bpl.Expr ReadHeap(IToken tok, Expr heap, Expr r, Expr f) {
      Contract.Requires(tok != null);
      Contract.Requires(heap != null);
      Contract.Requires(r != null);
      Contract.Requires(f != null);
      Contract.Ensures(Contract.Result<Bpl.NAryExpr>() != null);

      var res = new Bpl.NAryExpr(tok,
        new Bpl.FunctionCall(new Bpl.IdentifierExpr(tok, "read", Predef.BoxType)),
        new List<Bpl.Expr> { heap, r, f });
      res.Type = Predef.BoxType;
      return res;
    }

    public Bpl.NAryExpr ReadHeap(IToken tok, Expr heap, Expr r) {
      Contract.Requires(tok != null);
      Contract.Requires(heap != null);
      Contract.Requires(r != null);
      Contract.Ensures(Contract.Result<Bpl.NAryExpr>() != null);
      return new Bpl.NAryExpr(tok, new Bpl.MapSelect(tok, 1), new List<Bpl.Expr> { heap, r });
    }

    /// <summary>
    /// Returns update(h: Heap, r: ref, f: Field, v: Box) : Heap.
    /// </summary>
    public Boogie.NAryExpr UpdateHeap(IToken tok, Expr heap, Expr r, Expr f, Expr v) {
      Contract.Requires(tok != null);
      Contract.Requires(heap != null);
      Contract.Requires(r != null);
      Contract.Requires(f != null);
      Contract.Requires(v != null);
      Contract.Ensures(Contract.Result<Boogie.NAryExpr>() != null);


      return new Boogie.NAryExpr(tok,
        new Boogie.FunctionCall(new Boogie.IdentifierExpr(tok, "update", heap.Type)),
        new List<Boogie.Expr> { heap, r, f, ApplyBox(tok, v) });
    }
    
  /// <summary>
  /// For every revealed type (class or trait) C<T> that extends a trait J<G(T)>, add:
  ///   axiom (forall T: Ty, $o: ref ::
  ///       { $Is($o, C(T)) }
  ///       $o != null && $Is($o, C(T)) ==> $Is($o, J(G(T)));
  ///   axiom (forall T: Ty, $Heap: Heap, $o: ref ::
  ///       { $IsAlloc($o, C(T), $Heap) }
  ///       $o != null && $IsAlloc($o, C(T), $Heap) ==> $IsAlloc($o, J(G(T)), $Heap);
  /// Note:
  ///   It is sometimes useful also to be able to determine the _absence_ of trait-parent relationships.
  ///   For example, suppose one can tell from the looking at the "extends" clauses in a program
  ///   that a class C does not (directly or transitively) extend a trait T. Then, given variables c and t
  ///   of static types C and T, respectively, the verifier should be able to infer c != t. This is not
  ///   possible with the axioms below. It will require an axiomatization of _all_ possible parent traits, not just
  ///   saying that some are possible. When this becomes needed, the axiomatization will need to be
  ///   embellished.
  /// </summary>
  private void AddTraitParentAxioms() {
    foreach (ModuleDefinition m in program.RawModules()) {
      foreach (var c in m.TopLevelDecls.OfType<TopLevelDeclWithMembers>().Where(RevealedInScope)) {
        foreach (var parentTypeInExtendsClause in c.ParentTraits) {
          var childType = UserDefinedType.FromTopLevelDecl(c.tok, c);
          var parentType = (UserDefinedType)parentTypeInExtendsClause;
          if (parentType.IsRefType) {
            // use the nullable versions of the types
            Contract.Assert(childType.IsRefType);
            parentType = UserDefinedType.CreateNullableType(parentType);
          } else {
            childType = UserDefinedType.CreateNonNullTypeIfReferenceType(childType);
          }

          var bvarsTypeParameters = MkTyParamBinders(GetTypeParams(c), out _);

          // axioms with "$IsBox(...) ==> ..." and "$IsAllocBox(...) ==> ..."
          TypeBoundAxiomExpressions(c.tok, bvarsTypeParameters, childType, new List<Type>() { parentType },
            out var isBoxExpr, out var isAllocBoxExpr);

          var heapVar = BplBoundVar("$heap", Predef.HeapType, out var heap);
          var oVar = BplBoundVar("$o", TrType(childType), out var o);

          var oj = BoxifyForTraitParent(c.tok, o, ((UserDefinedType)parentType.NormalizeExpand()).ResolvedClass, childType);

          // axiom (forall T: Ty, $o: ref ::
          //     { $Is($o, C(T)) }
          //     $Is($o, C(T)) ==> $Is($o, J(G(T)));
          var isC = MkIs(o, childType);
          var isJ = MkIs(oj, parentType);
          var bvs = new List<Bpl.Variable>();
          bvs.AddRange(bvarsTypeParameters);
          bvs.Add(oVar);
          var tr = BplTrigger(isC);
          var body = BplImp(isC, isJ);

          sink.AddTopLevelDeclaration(new Bpl.Axiom(c.tok, new Bpl.ForallExpr(c.tok, bvs, tr, body),
            $"type axiom for trait parent: {childType.Name} extends {parentType}"));
          sink.AddTopLevelDeclaration(new Bpl.Axiom(c.tok, isBoxExpr));

          // axiom (forall T: Ty, $Heap: Heap, $o: ref ::
          //     { $IsAlloc($o, C(T), $Heap) }
          //     $IsAlloc($o, C(T), $Heap) ==> $IsAlloc($o, J(G(T)), $Heap);
          var isAllocC = MkIsAlloc(o, childType, heap);
          var isAllocJ = MkIsAlloc(oj, parentType, heap);
          bvs = new List<Bpl.Variable>();
          bvs.AddRange(bvarsTypeParameters);
          bvs.Add(oVar);
          bvs.Add(heapVar);
          tr = BplTrigger(isAllocC);
          body = BplImp(isAllocC, isAllocJ);
          sink.AddTopLevelDeclaration(new Bpl.Axiom(c.tok, new Bpl.ForallExpr(c.tok, bvs, tr, body),
            $"allocation axiom for trait parent: {childType.Name} extends {parentType}"));
          sink.AddTopLevelDeclaration(new Bpl.Axiom(c.tok, isAllocBoxExpr));
        }
      }
    }
  }
}