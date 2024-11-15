//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System.Collections.Generic;
using System.Numerics;
using System.Diagnostics.Contracts;
using Bpl = Microsoft.Boogie;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

public partial class BoogieGenerator {
  private void AddPreludeBoogieDefinitions() {
    
    foreach (var w in program.SystemModuleManager.Bitwidths) {
      // type axioms
      AddBitvectorTypeAxioms(w);
      // bitwise operations
      AddBitvectorFunction(w, "and_bv", "bvand");
      AddBitvectorFunction(w, "or_bv", "bvor");
      AddBitvectorFunction(w, "xor_bv", "bvxor");  // Z3 supports this, but it seems not to be in the SMT-LIB 2 standard
      AddBitvectorFunction(w, "not_bv", "bvnot", false);
      // arithmetic operations
      AddBitvectorFunction(w, "add_bv", "bvadd");
      AddBitvectorFunction(w, "sub_bv", "bvsub");  // Z3 supports this, but it seems not to be in the SMT-LIB 2 standard
      AddBitvectorFunction(w, "mul_bv", "bvmul");
      AddBitvectorFunction(w, "div_bv", "bvudiv");
      AddBitvectorFunction(w, "mod_bv", "bvurem");
      // comparisons
      AddBitvectorFunction(w, "lt_bv", "bvult", true, Bpl.Type.Bool, false);
      AddBitvectorFunction(w, "le_bv", "bvule", true, Bpl.Type.Bool, true);  // Z3 supports this, but it seems not to be in the SMT-LIB 2 standard
      AddBitvectorFunction(w, "ge_bv", "bvuge", true, Bpl.Type.Bool, true);  // Z3 supports this, but it seems not to be in the SMT-LIB 2 standard
      AddBitvectorFunction(w, "gt_bv", "bvugt", true, Bpl.Type.Bool, false);  // Z3 supports this, but it seems not to be in the SMT-LIB 2 standard
      // shifts
      AddBitvectorShiftFunction(w, "LeftShift_bv", "bvshl");
      AddBitvectorShiftFunction(w, "RightShift_bv", "bvlshr");
      // rotates
      AddBitvectorShiftFunction(w, "LeftRotate_bv", "ext_rotate_left");
      AddBitvectorShiftFunction(w, "RightRotate_bv", "ext_rotate_right");
      // conversion functions
      AddBitvectorNatConversionFunction(w);
    }

    foreach (TopLevelDecl d in program.SystemModuleManager.SystemModule.TopLevelDecls) {
      CurrentDeclaration = d;
      if (d is AbstractTypeDecl abstractType) {
        GetOrCreateTypeConstructor(abstractType);
        AddClassMembers(abstractType, true, true);
      } else if (d is NewtypeDecl) {
        var dd = (NewtypeDecl)d;
        AddTypeDecl(dd);
        AddClassMembers(dd, true, true);
      } else if (d is SubsetTypeDecl) {
        AddTypeDecl((SubsetTypeDecl)d);
      } else if (d is TypeSynonymDecl) {
        // do nothing, just bypass type synonyms in the translation
      } else if (d is DatatypeDecl) {
        var dd = (DatatypeDecl)d;
        AddDatatype(dd);
        AddClassMembers(dd, true, true);
      } else if (d is ArrowTypeDecl) {
        var ad = (ArrowTypeDecl)d;
        GetClassTyCon(ad);
        AddArrowTypeAxioms(ad);
      } else if (d is ClassLikeDecl) {
        var cl = (ClassLikeDecl)d;
        AddClassMembers(cl, true, true);
        if (cl.NonNullTypeDecl != null) {
          AddTypeDecl(cl.NonNullTypeDecl);
        }
      } else {
        Contract.Assert(d is ValuetypeDecl);
      }
    }
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
    AddBoxUnboxAxiom(tok, printableName, typeTerm, boogieType, new List<Variable>());

    // axiom (forall v: bv3 :: { $Is(v, TBitvector(3)) } $Is(v, TBitvector(3)));
    var vVar = BplBoundVar("v", boogieType, out var v);
    var bvs = new List<Variable>() { vVar };
    var isBv = MkIs(v, typeTerm);
    var tr = BplTrigger(isBv);
    sink.AddTopLevelDeclaration(new Bpl.Axiom(tok, new Bpl.ForallExpr(tok, bvs, tr, isBv)));

    // axiom (forall v: bv3, heap: Heap :: { $IsAlloc(v, TBitvector(3), h) } $IsAlloc(v, TBitvector(3), heap));
    vVar = BplBoundVar("v", boogieType, out v);
    var heapVar = BplBoundVar("heap", Predef.HeapType, out var heap);
    bvs = new List<Variable>() { vVar, heapVar };
    var isAllocBv = MkIsAlloc(v, typeTerm, heap);
    tr = BplTrigger(isAllocBv);
    sink.AddTopLevelDeclaration(new Bpl.Axiom(tok, new Bpl.ForallExpr(tok, bvs, tr, isAllocBv)));
  }

  /// <summary>
  /// Declare and add to the sink a Boogie function named "namePrefix + w".
  /// If "binary", then the function takes two arguments; otherwise, it takes one.  Arguments have the type
  /// corresponding to the Dafny type for w-width bitvectors.
  /// The function's result type is the same as the argument type, unless "resultType" is non-null, in which
  /// case the function's result type is "resultType".
  /// For w > 0:
  ///     Attach an attribute {:bvbuiltin smtFunctionName}.
  /// For w == 0:
  ///     Attach an attribute {:inline} and add a .Body to the function.
  ///     If "resultType" is null, then use 0 as the body; otherwise, use "bodyForBv0" as the body (which
  ///     assumes "resultType" is actually Bpl.Type.Bool).
  /// </summary>
  private void AddBitvectorFunction(int w, string namePrefix, string smtFunctionName, bool binary = true, Bpl.Type resultType = null, bool bodyForBv0 = false) {
    Contract.Requires(0 <= w);
    Contract.Requires(namePrefix != null);
    Contract.Requires(smtFunctionName != null);
    var tok = Token.NoToken;
    var t = BplBvType(w);
    List<Bpl.Variable> args;
    if (binary) {
      var a0 = BplFormalVar(null, t, true);
      var a1 = BplFormalVar(null, t, true);
      args = new List<Variable>() { a0, a1 };
    } else {
      var a0 = BplFormalVar(null, t, true);
      args = new List<Variable>() { a0 };
    }
    var r = BplFormalVar(null, resultType ?? t, false);
    Bpl.QKeyValue attr;
    if (w == 0) {
      attr = InlineAttribute(tok);
    } else {
      attr = new Bpl.QKeyValue(tok, "bvbuiltin", new List<object>() { smtFunctionName }, null);
    }
    var func = new Bpl.Function(tok, namePrefix + w, new List<TypeVariable>(), args, r, null, attr);
    if (w == 0) {
      if (resultType != null) {
        func.Body = Bpl.Expr.Literal(bodyForBv0);
      } else {
        func.Body = BplBvLiteralExpr(tok, BaseTypes.BigNum.ZERO, w);
      }
    }
    sink.AddTopLevelDeclaration(func);
  }

  private void AddBitvectorShiftFunction(int w, string namePrefix, string smtFunctionName) {
    Contract.Requires(0 <= w);
    Contract.Requires(namePrefix != null);
    Contract.Requires(smtFunctionName != null);
    var tok = Token.NoToken;
    var t = BplBvType(w);
    List<Bpl.Variable> args;
    var a0 = BplFormalVar(null, t, true);
    var a1 = BplFormalVar(null, t, true);
    args = new List<Variable>() { a0, a1 };
    var r = BplFormalVar(null, t, false);
    Bpl.QKeyValue attr;
    if (w == 0) {
      attr = InlineAttribute(tok);
    } else {
      attr = new Bpl.QKeyValue(tok, "bvbuiltin", new List<object>() { smtFunctionName }, null);
    }
    var func = new Bpl.Function(tok, namePrefix + w, new List<TypeVariable>(), args, r, null, attr);
    if (w == 0) {
      func.Body = BplBvLiteralExpr(tok, BaseTypes.BigNum.ZERO, w);
    }
    sink.AddTopLevelDeclaration(func);
  }

  private void AddBitvectorNatConversionFunction(int w) {
    Contract.Requires(0 <= w);
    var tok = Token.NoToken;
    var bv = BplBvType(w);
    Bpl.QKeyValue attr;
    Bpl.Function func;

    // function {:bvbuiltin "(_ int2bv 67)"} nat_to_bv67(int) : bv67;
    // OR:
    // function {:inline} nat_to_bv0(int) : Bv0 { ZERO }
    if (w == 0) {
      attr = InlineAttribute(tok);
    } else {
      var smt_int2bv = string.Format("(_ int2bv {0})", w);
      attr = new Bpl.QKeyValue(tok, "bvbuiltin", new List<object>() { smt_int2bv }, null);  // SMT-LIB 2 calls this function nat2bv, but Z3 apparently calls it int2bv
    }
    func = new Bpl.Function(tok, "nat_to_bv" + w, new List<TypeVariable>(),
      new List<Variable>() { BplFormalVar(null, Bpl.Type.Int, true) }, BplFormalVar(null, bv, false),
      null, attr);
    if (w == 0) {
      func.Body = BplBvLiteralExpr(tok, BaseTypes.BigNum.ZERO, w);
    }
    sink.AddTopLevelDeclaration(func);

    if (w == 0) {
      // function {:inline} nat_from_bv0_smt(Bv0) : int { 0 }
      attr = InlineAttribute(tok);
      func = new Bpl.Function(tok, "nat_from_bv" + w, new List<TypeVariable>(),
        new List<Variable>() { BplFormalVar(null, bv, true) }, BplFormalVar(null, Bpl.Type.Int, false),
        null, attr);
      func.Body = Bpl.Expr.Literal(0);
      sink.AddTopLevelDeclaration(func);
    } else {
      // function {:bvbuiltin "bv2int"} smt_nat_from_bv67(bv67) : int;
      attr = new Bpl.QKeyValue(tok, "bvbuiltin", new List<object>() { "bv2int" }, null);  // SMT-LIB 2 calls this function bv2nat, but Z3 apparently calls it bv2int
      var smtFunc = new Bpl.Function(tok, "smt_nat_from_bv" + w, new List<TypeVariable>(),
        new List<Variable>() { BplFormalVar(null, bv, true) }, BplFormalVar(null, Bpl.Type.Int, false),
        null, attr);
      sink.AddTopLevelDeclaration(smtFunc);
      // function nat_from_bv67(bv67) : int;
      func = new Bpl.Function(tok, "nat_from_bv" + w, new List<TypeVariable>(),
        new List<Variable>() { BplFormalVar(null, bv, true) }, BplFormalVar(null, Bpl.Type.Int, false),
        null, null);
      sink.AddTopLevelDeclaration(func);
      // axiom (forall b: bv67 :: { nat_from_bv67(b) }
      //          0 <= nat_from_bv67(b) && nat_from_bv67(b) < 0x8_0000_0000_0000_0000 &&
      //          nat_from_bv67(b) == smt_nat_from_bv67(b));
      var bVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "b", BplBvType(w)));
      var b = new Bpl.IdentifierExpr(tok, bVar);
      var bv2nat = FunctionCall(tok, "nat_from_bv" + w, Bpl.Type.Int, b);
      var smt_bv2nat = FunctionCall(tok, "smt_nat_from_bv" + w, Bpl.Type.Int, b);
      var body = BplAnd(BplAnd(
        Bpl.Expr.Le(Bpl.Expr.Literal(0), bv2nat),
        Bpl.Expr.Lt(bv2nat, Bpl.Expr.Literal(BaseTypes.BigNum.FromBigInt(BigInteger.One << w)))),
        Bpl.Expr.Eq(bv2nat, smt_bv2nat));
      var ax = new Bpl.ForallExpr(tok, new List<Variable>() { bVar }, BplTrigger(bv2nat), body);
      sink.AddTopLevelDeclaration(new Bpl.Axiom(tok, ax));
    }
  }
}