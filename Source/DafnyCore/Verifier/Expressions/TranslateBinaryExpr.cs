using System;
using System.Collections.Generic;

namespace Microsoft.Dafny;

using System.Diagnostics.Contracts;
using Boogie;

public partial class BoogieGenerator {
  public partial class ExpressionTranslator {

    private Expr TranslateBinaryExpr(BinaryExpr binaryExpr) {
      var e0Type = binaryExpr.E0.Type.NormalizeToAncestorType(); // used when making decisions about what Boogie operator/functions to use
      bool isReal = e0Type.IsNumericBased(Type.NumericPersuasion.Real);
      int bvWidth = e0Type.IsBitVectorType ? e0Type.AsBitVectorType.Width : -1;  // -1 indicates "not a bitvector type"
      Expr e0 = TrExpr(binaryExpr.E0);
      if (binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.InSet) {
        return TrInSet(GetToken(binaryExpr), e0, binaryExpr.E1, binaryExpr.E0.Type, binaryExpr.E1.Type.NormalizeToAncestorType().AsSetType.Finite, false, out var pr);  // let TrInSet translate e.E1
      } else if (binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.NotInSet) {
        Expr arg = TrInSet(GetToken(binaryExpr), e0, binaryExpr.E1, binaryExpr.E0.Type, binaryExpr.E1.Type.NormalizeToAncestorType().AsSetType.Finite, false, out var pr);  // let TrInSet translate e.E1
        return Expr.Unary(GetToken(binaryExpr), UnaryOperator.Opcode.Not, arg);
      } else if (binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.InMultiSet) {
        return TrInMultiSet(GetToken(binaryExpr), e0, binaryExpr.E1, binaryExpr.E0.Type, false); // let TrInMultiSet translate e.E1
      } else if (binaryExpr.ResolvedOp == BinaryExpr.ResolvedOpcode.NotInMultiSet) {
        Expr arg = TrInMultiSet(GetToken(binaryExpr), e0, binaryExpr.E1, binaryExpr.E0.Type, false);  // let TrInMultiSet translate e.E1
        return Expr.Unary(GetToken(binaryExpr), UnaryOperator.Opcode.Not, arg);
      }
      Expr e1 = TrExpr(binaryExpr.E1);
      BinaryOperator.Opcode bOpcode;
      Boogie.Type typ;
      var oe0 = e0;
      var oe1 = e1;
      var lit0 = GetLit(e0);
      var lit1 = GetLit(e1);
      bool liftLit = BoogieGenerator.IsLit(e0) && BoogieGenerator.IsLit(e1);
      // NOTE(namin): We usually avoid keeping literals, because their presence might mess up triggers that do not expect them.
      //              Still for equality-related operations, it's useful to keep them instead of lifting them, so that they can be propagated.
      bool keepLits = false;
      if (lit0 != null) {
        e0 = lit0;
      }
      if (lit1 != null) {
        e1 = lit1;
      }
      switch (binaryExpr.ResolvedOp) {
        case BinaryExpr.ResolvedOpcode.Iff:
          typ = Boogie.Type.Bool;
          bOpcode = BinaryOperator.Opcode.Iff; break;
        case BinaryExpr.ResolvedOpcode.Imp:
          typ = Boogie.Type.Bool;
          bOpcode = BinaryOperator.Opcode.Imp; break;
        case BinaryExpr.ResolvedOpcode.And:
          typ = Boogie.Type.Bool;
          bOpcode = BinaryOperator.Opcode.And; break;
        case BinaryExpr.ResolvedOpcode.Or:
          typ = Boogie.Type.Bool;
          bOpcode = BinaryOperator.Opcode.Or; break;

        case BinaryExpr.ResolvedOpcode.EqCommon:
          keepLits = true;
          if (ModeledAsBoxType(binaryExpr.E0.Type)) {
            e1 = BoxIfNecessary(binaryExpr.Origin, e1, binaryExpr.E1.Type);
            oe1 = BoxIfNecessary(binaryExpr.Origin, oe1, binaryExpr.E1.Type);
          } else if (ModeledAsBoxType(binaryExpr.E1.Type)) {
            e0 = BoxIfNecessary(binaryExpr.Origin, e0, binaryExpr.E0.Type);
            oe0 = BoxIfNecessary(binaryExpr.Origin, oe0, binaryExpr.E0.Type);
          }
          if (binaryExpr.E0.Type.IsCoDatatype && binaryExpr.E1.Type.IsCoDatatype) {
            var e0args = binaryExpr.E0.Type.NormalizeExpand().TypeArgs;
            var e1args = binaryExpr.E1.Type.NormalizeExpand().TypeArgs;
            return BoogieGenerator.CoEqualCall(binaryExpr.E0.Type.AsCoDatatype, e0args, e1args, null,
              layerInterCluster.LayerN((int)FuelSetting.FuelAmount.HIGH), e0, e1, GetToken(binaryExpr));
          }
          if (binaryExpr.E0.Type.IsIndDatatype && binaryExpr.E1.Type.IsIndDatatype) {
            return BoogieGenerator.TypeSpecificEqual(GetToken(binaryExpr), binaryExpr.E0.Type, e0, e1);
          }
          typ = Boogie.Type.Bool;
          bOpcode = BinaryOperator.Opcode.Eq;
          break;
        case BinaryExpr.ResolvedOpcode.NeqCommon:
          if (ModeledAsBoxType(binaryExpr.E0.Type)) {
            e1 = BoxIfNecessary(binaryExpr.Origin, e1, binaryExpr.E1.Type);
            oe1 = BoxIfNecessary(binaryExpr.Origin, oe1, binaryExpr.E1.Type);
          } else if (ModeledAsBoxType(binaryExpr.E1.Type)) {
            e0 = BoxIfNecessary(binaryExpr.Origin, e0, binaryExpr.E0.Type);
            oe0 = BoxIfNecessary(binaryExpr.Origin, oe0, binaryExpr.E0.Type);
          }
          if (binaryExpr.E0.Type.IsCoDatatype && binaryExpr.E1.Type.IsCoDatatype) {
            var e0args = binaryExpr.E0.Type.NormalizeExpand().TypeArgs;
            var e1args = binaryExpr.E1.Type.NormalizeExpand().TypeArgs;
            var eq = BoogieGenerator.CoEqualCall(binaryExpr.E0.Type.AsCoDatatype, e0args, e1args, null,
              layerInterCluster.LayerN((int)FuelSetting.FuelAmount.HIGH), e0, e1, GetToken(binaryExpr));
            return Expr.Unary(GetToken(binaryExpr), UnaryOperator.Opcode.Not, eq);
          }
          if (binaryExpr.E0.Type.IsIndDatatype && binaryExpr.E1.Type.IsIndDatatype) {
            var eq = BoogieGenerator.TypeSpecificEqual(GetToken(binaryExpr), binaryExpr.E0.Type, e0, e1);
            return Expr.Unary(GetToken(binaryExpr), UnaryOperator.Opcode.Not, eq);
          }
          typ = Boogie.Type.Bool;
          bOpcode = BinaryOperator.Opcode.Neq;
          break;
        case BinaryExpr.ResolvedOpcode.Lt:
          if (0 <= bvWidth) {
            return TrToFunctionCall(GetToken(binaryExpr), "lt_bv" + bvWidth, Boogie.Type.Bool, e0, e1, liftLit);
          } else if (e0Type.IsBigOrdinalType) {
            return FunctionCall(GetToken(binaryExpr), "ORD#Less", Boogie.Type.Bool, e0, e1);
          } else if (isReal || !BoogieGenerator.DisableNonLinearArithmetic) {
            typ = Boogie.Type.Bool;
            bOpcode = BinaryOperator.Opcode.Lt;
            break;
          } else {
            return TrToFunctionCall(GetToken(binaryExpr), "INTERNAL_lt_boogie", Boogie.Type.Bool, e0, e1, liftLit);
          }
        case BinaryExpr.ResolvedOpcode.LessThanLimit:
          return FunctionCall(GetToken(binaryExpr), "ORD#LessThanLimit", Boogie.Type.Bool, e0, e1);
        case BinaryExpr.ResolvedOpcode.Le:
          keepLits = true;
          if (0 <= bvWidth) {
            return TrToFunctionCall(GetToken(binaryExpr), "le_bv" + bvWidth, Boogie.Type.Bool, e0, e1, false);
          } else if (e0Type.IsBigOrdinalType) {
            var less = FunctionCall(GetToken(binaryExpr), "ORD#Less", Boogie.Type.Bool, e0, e1);
            var eq = Expr.Eq(e0, e1);
            return BplOr(eq, less);
          } else if (isReal || !BoogieGenerator.DisableNonLinearArithmetic) {
            typ = Boogie.Type.Bool;
            bOpcode = BinaryOperator.Opcode.Le;
            break;
          } else {
            return TrToFunctionCall(GetToken(binaryExpr), "INTERNAL_le_boogie", Boogie.Type.Bool, e0, e1, false);
          }
        case BinaryExpr.ResolvedOpcode.Ge:
          keepLits = true;
          if (0 <= bvWidth) {
            return TrToFunctionCall(GetToken(binaryExpr), "ge_bv" + bvWidth, Boogie.Type.Bool, e0, e1, false);
          } else if (e0Type.IsBigOrdinalType) {
            var less = FunctionCall(GetToken(binaryExpr), "ORD#Less", Boogie.Type.Bool, e1, e0);
            var eq = Expr.Eq(e1, e0);
            return BplOr(eq, less);
          } else if (isReal || !BoogieGenerator.DisableNonLinearArithmetic) {
            typ = Boogie.Type.Bool;
            bOpcode = BinaryOperator.Opcode.Ge;
            break;
          } else {
            return TrToFunctionCall(GetToken(binaryExpr), "INTERNAL_ge_boogie", Boogie.Type.Bool, e0, e1, false);
          }
        case BinaryExpr.ResolvedOpcode.Gt:
          if (0 <= bvWidth) {
            return TrToFunctionCall(GetToken(binaryExpr), "gt_bv" + bvWidth, Boogie.Type.Bool, e0, e1, liftLit);
          } else if (e0Type.IsBigOrdinalType) {
            return FunctionCall(GetToken(binaryExpr), "ORD#Less", Boogie.Type.Bool, e1, e0);
          } else if (isReal || !BoogieGenerator.DisableNonLinearArithmetic) {
            typ = Boogie.Type.Bool;
            bOpcode = BinaryOperator.Opcode.Gt;
            break;
          } else {
            return TrToFunctionCall(GetToken(binaryExpr), "INTERNAL_gt_boogie", Boogie.Type.Bool, e0, e1, liftLit);
          }

        case BinaryExpr.ResolvedOpcode.Add:
          if (0 <= bvWidth) {
            return TrToFunctionCall(GetToken(binaryExpr), "add_bv" + bvWidth, BoogieGenerator.BplBvType(bvWidth), e0, e1, liftLit);
          } else if (e0Type.IsBigOrdinalType) {
            return TrToFunctionCall(GetToken(binaryExpr), "ORD#Plus", Predef.BigOrdinalType, e0, e1, liftLit);
          } else if (e0Type.IsCharType) {
            return TrToFunctionCall(GetToken(binaryExpr), "char#Plus", Predef.CharType, e0, e1, liftLit);
          } else if (!isReal && BoogieGenerator.DisableNonLinearArithmetic) {
            return TrToFunctionCall(GetToken(binaryExpr), "INTERNAL_add_boogie", Boogie.Type.Int, e0, e1, liftLit);
          } else if (!isReal && (options.ArithMode == 2 || 5 <= options.ArithMode)) {
            return TrToFunctionCall(GetToken(binaryExpr), "Add", Boogie.Type.Int, oe0, oe1, liftLit);
          } else {
            typ = isReal ? Boogie.Type.Real : Boogie.Type.Int;
            bOpcode = BinaryOperator.Opcode.Add;
            break;
          }
        case BinaryExpr.ResolvedOpcode.Sub:
          if (0 <= bvWidth) {
            return TrToFunctionCall(GetToken(binaryExpr), "sub_bv" + bvWidth, BoogieGenerator.BplBvType(bvWidth), e0, e1, liftLit);
          } else if (e0Type.IsBigOrdinalType) {
            return TrToFunctionCall(GetToken(binaryExpr), "ORD#Minus", Predef.BigOrdinalType, e0, e1, liftLit);
          } else if (e0Type.IsCharType) {
            return TrToFunctionCall(GetToken(binaryExpr), "char#Minus", Predef.CharType, e0, e1, liftLit);
          } else if (!isReal && BoogieGenerator.DisableNonLinearArithmetic) {
            return TrToFunctionCall(GetToken(binaryExpr), "INTERNAL_sub_boogie", Boogie.Type.Int, e0, e1, liftLit);
          } else if (!isReal && (options.ArithMode == 2 || 5 <= options.ArithMode)) {
            return TrToFunctionCall(GetToken(binaryExpr), "Sub", Boogie.Type.Int, oe0, oe1, liftLit);
          } else {
            typ = isReal ? Boogie.Type.Real : Boogie.Type.Int;
            bOpcode = BinaryOperator.Opcode.Sub;
            break;
          }
        case BinaryExpr.ResolvedOpcode.Mul:
          if (0 <= bvWidth) {
            return TrToFunctionCall(GetToken(binaryExpr), "mul_bv" + bvWidth, BoogieGenerator.BplBvType(bvWidth), e0, e1, liftLit);
          } else if (!isReal && BoogieGenerator.DisableNonLinearArithmetic) {
            return TrToFunctionCall(GetToken(binaryExpr), "INTERNAL_mul_boogie", Boogie.Type.Int, e0, e1, liftLit);
          } else if (!isReal && options.ArithMode != 0 && options.ArithMode != 3) {
            return TrToFunctionCall(GetToken(binaryExpr), "Mul", Boogie.Type.Int, oe0, oe1, liftLit);
          } else {
            typ = isReal ? Boogie.Type.Real : Boogie.Type.Int;
            bOpcode = BinaryOperator.Opcode.Mul;
            break;
          }
        case BinaryExpr.ResolvedOpcode.Div:
          if (0 <= bvWidth) {
            return TrToFunctionCall(GetToken(binaryExpr), "div_bv" + bvWidth, BoogieGenerator.BplBvType(bvWidth), e0, e1, liftLit);
          } else if (!isReal && BoogieGenerator.DisableNonLinearArithmetic && !isReal) {
            return TrToFunctionCall(GetToken(binaryExpr), "INTERNAL_div_boogie", Boogie.Type.Int, e0, e1, liftLit);
          } else if (!isReal && options.ArithMode != 0 && options.ArithMode != 3) {
            return TrToFunctionCall(GetToken(binaryExpr), "Div", Boogie.Type.Int, e0, oe1, liftLit);
          } else if (isReal) {
            typ = Boogie.Type.Real;
            bOpcode = BinaryOperator.Opcode.RealDiv;
            break;
          } else {
            typ = Boogie.Type.Int;
            bOpcode = BinaryOperator.Opcode.Div;
            break;
          }
        case BinaryExpr.ResolvedOpcode.Mod:
          if (0 <= bvWidth) {
            return TrToFunctionCall(GetToken(binaryExpr), "mod_bv" + bvWidth, BoogieGenerator.BplBvType(bvWidth), e0, e1, liftLit);
          } else if (BoogieGenerator.DisableNonLinearArithmetic && !isReal) {
            return TrToFunctionCall(GetToken(binaryExpr), "INTERNAL_mod_boogie", Boogie.Type.Int, e0, e1, liftLit);
          } else if (!isReal && options.ArithMode != 0 && options.ArithMode != 3) {
            return TrToFunctionCall(GetToken(binaryExpr), "Mod", Boogie.Type.Int, e0, oe1, liftLit);
          } else {
            typ = isReal ? Boogie.Type.Real : Boogie.Type.Int;
            bOpcode = BinaryOperator.Opcode.Mod;
            break;
          }

        case BinaryExpr.ResolvedOpcode.LeftShift: {
            Contract.Assert(0 <= bvWidth);
            return TrToFunctionCall(GetToken(binaryExpr), "LeftShift_bv" + bvWidth, BoogieGenerator.BplBvType(bvWidth), e0, BoogieGenerator.ConvertExpression(GetToken(binaryExpr), e1, binaryExpr.E1.Type, binaryExpr.Type), liftLit);
          }
        case BinaryExpr.ResolvedOpcode.RightShift: {
            Contract.Assert(0 <= bvWidth);
            return TrToFunctionCall(GetToken(binaryExpr), "RightShift_bv" + bvWidth, BoogieGenerator.BplBvType(bvWidth), e0, BoogieGenerator.ConvertExpression(GetToken(binaryExpr), e1, binaryExpr.E1.Type, binaryExpr.Type), liftLit);
          }
        case BinaryExpr.ResolvedOpcode.BitwiseAnd: {
            Contract.Assert(0 <= bvWidth);
            return TrToFunctionCall(GetToken(binaryExpr), "and_bv" + bvWidth, BoogieGenerator.BplBvType(bvWidth), e0, e1, liftLit);
          }
        case BinaryExpr.ResolvedOpcode.BitwiseOr: {
            Contract.Assert(0 <= bvWidth);
            return TrToFunctionCall(GetToken(binaryExpr), "or_bv" + bvWidth, BoogieGenerator.BplBvType(bvWidth), e0, e1, liftLit);
          }
        case BinaryExpr.ResolvedOpcode.BitwiseXor: {
            Contract.Assert(0 <= bvWidth);
            return TrToFunctionCall(GetToken(binaryExpr), "xor_bv" + bvWidth, BoogieGenerator.BplBvType(bvWidth), e0, e1, liftLit);
          }

        case BinaryExpr.ResolvedOpcode.LtChar:
        case BinaryExpr.ResolvedOpcode.LeChar:
        case BinaryExpr.ResolvedOpcode.GeChar:
        case BinaryExpr.ResolvedOpcode.GtChar: {
            // work off the original operands (that is, allow them to be lit-wrapped)
            var operand0 = BoogieGenerator.FunctionCall(e0.tok, BuiltinFunction.CharToInt, null, oe0);
            var operand1 = BoogieGenerator.FunctionCall(e0.tok, BuiltinFunction.CharToInt, null, oe1);
            BinaryOperator.Opcode bOp;
            switch (binaryExpr.ResolvedOp) {
              case BinaryExpr.ResolvedOpcode.LtChar: bOp = BinaryOperator.Opcode.Lt; break;
              case BinaryExpr.ResolvedOpcode.LeChar: bOp = BinaryOperator.Opcode.Le; break;
              case BinaryExpr.ResolvedOpcode.GeChar: bOp = BinaryOperator.Opcode.Ge; break;
              case BinaryExpr.ResolvedOpcode.GtChar: bOp = BinaryOperator.Opcode.Gt; break;
              default:
                Contract.Assert(false);  // unexpected case
                throw new Cce.UnreachableException();  // to please compiler
            }
            return Expr.Binary(GetToken(binaryExpr), bOp, operand0, operand1);
          }

        case BinaryExpr.ResolvedOpcode.SetEq:
        case BinaryExpr.ResolvedOpcode.MultiSetEq:
        case BinaryExpr.ResolvedOpcode.SeqEq:
        case BinaryExpr.ResolvedOpcode.MapEq:
          return BoogieGenerator.TypeSpecificEqual(GetToken(binaryExpr), binaryExpr.E0.Type, e0, e1);
        case BinaryExpr.ResolvedOpcode.SetNeq:
        case BinaryExpr.ResolvedOpcode.MultiSetNeq:
        case BinaryExpr.ResolvedOpcode.SeqNeq:
        case BinaryExpr.ResolvedOpcode.MapNeq:
          return Expr.Unary(GetToken(binaryExpr), UnaryOperator.Opcode.Not, BoogieGenerator.TypeSpecificEqual(GetToken(binaryExpr), binaryExpr.E0.Type, e0, e1));

        case BinaryExpr.ResolvedOpcode.ProperSubset: {
            return BoogieGenerator.ProperSubset(GetToken(binaryExpr), e0, e1, binaryExpr.E0.Type.NormalizeToAncestorType().AsSetType.Finite);
          }
        case BinaryExpr.ResolvedOpcode.Subset: {
            bool finite = binaryExpr.E1.Type.NormalizeToAncestorType().AsSetType.Finite;
            var f = finite ? BuiltinFunction.SetSubset : BuiltinFunction.ISetSubset;
            return BoogieGenerator.FunctionCall(GetToken(binaryExpr), f, null, e0, e1);
          }
        case BinaryExpr.ResolvedOpcode.Superset: {
            bool finite = binaryExpr.E1.Type.NormalizeToAncestorType().AsSetType.Finite;
            var f = finite ? BuiltinFunction.SetSubset : BuiltinFunction.ISetSubset;
            return BoogieGenerator.FunctionCall(GetToken(binaryExpr), f, null, e1, e0);
          }
        case BinaryExpr.ResolvedOpcode.ProperSuperset:
          return BoogieGenerator.ProperSubset(GetToken(binaryExpr), e1, e0, binaryExpr.E0.Type.NormalizeToAncestorType().AsSetType.Finite);
        case BinaryExpr.ResolvedOpcode.Disjoint: {
            bool finite = binaryExpr.E1.Type.NormalizeToAncestorType().AsSetType.Finite;
            var f = finite ? BuiltinFunction.SetDisjoint : BuiltinFunction.ISetDisjoint;
            return BoogieGenerator.FunctionCall(GetToken(binaryExpr), f, null, e0, e1);
          }
        case BinaryExpr.ResolvedOpcode.InSet:
          Contract.Assert(false); throw new Cce.UnreachableException();  // this case handled above
        case BinaryExpr.ResolvedOpcode.NotInSet:
          Contract.Assert(false); throw new Cce.UnreachableException();  // this case handled above
        case BinaryExpr.ResolvedOpcode.Union: {
            var setType = binaryExpr.Type.NormalizeToAncestorType().AsSetType;
            bool finite = setType.Finite;
            var f = finite ? BuiltinFunction.SetUnion : BuiltinFunction.ISetUnion;
            return BoogieGenerator.FunctionCall(GetToken(binaryExpr), f, BoogieGenerator.TrType(setType.Arg), e0, e1);
          }
        case BinaryExpr.ResolvedOpcode.Intersection: {
            var setType = binaryExpr.Type.NormalizeToAncestorType().AsSetType;
            bool finite = setType.Finite;
            var f = finite ? BuiltinFunction.SetIntersection : BuiltinFunction.ISetIntersection;
            return BoogieGenerator.FunctionCall(GetToken(binaryExpr), f, BoogieGenerator.TrType(setType.Arg), e0, e1);
          }
        case BinaryExpr.ResolvedOpcode.SetDifference: {
            var setType = binaryExpr.Type.NormalizeToAncestorType().AsSetType;
            bool finite = setType.Finite;
            var f = finite ? BuiltinFunction.SetDifference : BuiltinFunction.ISetDifference;
            return BoogieGenerator.FunctionCall(GetToken(binaryExpr), f, BoogieGenerator.TrType(setType.Arg), e0, e1);
          }
        case BinaryExpr.ResolvedOpcode.ProperMultiSubset:
          return BoogieGenerator.ProperMultiset(GetToken(binaryExpr), e0, e1);
        case BinaryExpr.ResolvedOpcode.MultiSubset:
          return BoogieGenerator.FunctionCall(GetToken(binaryExpr), BuiltinFunction.MultiSetSubset, null, e0, e1);
        case BinaryExpr.ResolvedOpcode.MultiSuperset:
          return BoogieGenerator.FunctionCall(GetToken(binaryExpr), BuiltinFunction.MultiSetSubset, null, e1, e0);
        case BinaryExpr.ResolvedOpcode.ProperMultiSuperset:
          return BoogieGenerator.ProperMultiset(GetToken(binaryExpr), e1, e0);
        case BinaryExpr.ResolvedOpcode.MultiSetDisjoint:
          return BoogieGenerator.FunctionCall(GetToken(binaryExpr), BuiltinFunction.MultiSetDisjoint, null, e0, e1);
        case BinaryExpr.ResolvedOpcode.InMultiSet:
          Contract.Assert(false); throw new Cce.UnreachableException();  // this case handled above
        case BinaryExpr.ResolvedOpcode.NotInMultiSet:
          Contract.Assert(false); throw new Cce.UnreachableException();  // this case handled above
        case BinaryExpr.ResolvedOpcode.MultiSetUnion:
          return BoogieGenerator.FunctionCall(GetToken(binaryExpr), BuiltinFunction.MultiSetUnion,
            BoogieGenerator.TrType(binaryExpr.Type.NormalizeToAncestorType().AsMultiSetType.Arg), e0, e1);
        case BinaryExpr.ResolvedOpcode.MultiSetIntersection:
          return BoogieGenerator.FunctionCall(GetToken(binaryExpr), BuiltinFunction.MultiSetIntersection,
            BoogieGenerator.TrType(binaryExpr.Type.NormalizeToAncestorType().AsMultiSetType.Arg), e0, e1);
        case BinaryExpr.ResolvedOpcode.MultiSetDifference:
          return BoogieGenerator.FunctionCall(GetToken(binaryExpr), BuiltinFunction.MultiSetDifference,
            BoogieGenerator.TrType(binaryExpr.Type.NormalizeToAncestorType().AsMultiSetType.Arg), e0, e1);

        case BinaryExpr.ResolvedOpcode.ProperPrefix:
          return BoogieGenerator.ProperPrefix(GetToken(binaryExpr), e0, e1);
        case BinaryExpr.ResolvedOpcode.Prefix: {
            Expr len0 = BoogieGenerator.FunctionCall(GetToken(binaryExpr), BuiltinFunction.SeqLength, null, e0);
            Expr len1 = BoogieGenerator.FunctionCall(GetToken(binaryExpr), BuiltinFunction.SeqLength, null, e1);
            return Expr.Binary(GetToken(binaryExpr), BinaryOperator.Opcode.And,
              Expr.Le(len0, len1),
              BoogieGenerator.FunctionCall(GetToken(binaryExpr), BuiltinFunction.SeqSameUntil, null, e0, e1, len0));
          }
        case BinaryExpr.ResolvedOpcode.Concat:
          return BoogieGenerator.FunctionCall(GetToken(binaryExpr), BuiltinFunction.SeqAppend,
            BoogieGenerator.TrType(binaryExpr.Type.NormalizeToAncestorType().AsSeqType.Arg), e0, e1);
        case BinaryExpr.ResolvedOpcode.InSeq:
          return BoogieGenerator.FunctionCall(GetToken(binaryExpr), BuiltinFunction.SeqContains, null, e1,
            BoxIfNecessary(GetToken(binaryExpr), e0, binaryExpr.E0.Type));
        case BinaryExpr.ResolvedOpcode.NotInSeq:
          Expr arg = BoogieGenerator.FunctionCall(GetToken(binaryExpr), BuiltinFunction.SeqContains, null, e1,
            BoxIfNecessary(GetToken(binaryExpr), e0, binaryExpr.E0.Type));
          return Expr.Unary(GetToken(binaryExpr), UnaryOperator.Opcode.Not, arg);
        case BinaryExpr.ResolvedOpcode.InMap: {
            bool finite = binaryExpr.E1.Type.NormalizeToAncestorType().AsMapType.Finite;
            var f = finite ? BuiltinFunction.MapDomain : BuiltinFunction.IMapDomain;
            return BoogieGenerator.IsSetMember(GetToken(binaryExpr),
              BoogieGenerator.FunctionCall(GetToken(binaryExpr), f, finite ? Predef.MapType : Predef.IMapType, e1),
              BoxIfNecessary(GetToken(binaryExpr), e0, binaryExpr.E0.Type),
              finite);
          }
        case BinaryExpr.ResolvedOpcode.NotInMap: {
            bool finite = binaryExpr.E1.Type.NormalizeToAncestorType().AsMapType.Finite;
            var f = finite ? BuiltinFunction.MapDomain : BuiltinFunction.IMapDomain;
            Expr inMap = BoogieGenerator.IsSetMember(GetToken(binaryExpr),
              BoogieGenerator.FunctionCall(GetToken(binaryExpr), f, finite ? Predef.MapType : Predef.IMapType, e1),
              BoxIfNecessary(GetToken(binaryExpr), e0, binaryExpr.E0.Type),
              finite);
            return Expr.Unary(GetToken(binaryExpr), UnaryOperator.Opcode.Not, inMap);
          }
        case BinaryExpr.ResolvedOpcode.MapMerge: {
            bool finite = e0Type.NormalizeToAncestorType().AsMapType.Finite;
            var f = finite ? "Map#Merge" : "IMap#Merge";
            return FunctionCall(GetToken(binaryExpr), f, BoogieGenerator.TrType(binaryExpr.Type), e0, e1);
          }
        case BinaryExpr.ResolvedOpcode.MapSubtraction: {
            bool finite = e0Type.NormalizeToAncestorType().AsMapType.Finite;
            var f = finite ? "Map#Subtract" : "IMap#Subtract";
            return FunctionCall(GetToken(binaryExpr), f, BoogieGenerator.TrType(binaryExpr.Type), e0, e1);
          }

        case BinaryExpr.ResolvedOpcode.RankLt:
          return Expr.Binary(GetToken(binaryExpr), BinaryOperator.Opcode.Lt,
            BoogieGenerator.FunctionCall(GetToken(binaryExpr), e0Type.IsDatatype ? BuiltinFunction.DtRank : BuiltinFunction.BoxRank, null, e0),
            BoogieGenerator.FunctionCall(GetToken(binaryExpr), BuiltinFunction.DtRank, null, e1));
        case BinaryExpr.ResolvedOpcode.RankGt:
          return Expr.Binary(GetToken(binaryExpr), BinaryOperator.Opcode.Gt,
            BoogieGenerator.FunctionCall(GetToken(binaryExpr), BuiltinFunction.DtRank, null, e0),
            BoogieGenerator.FunctionCall(GetToken(binaryExpr), binaryExpr.E1.Type.IsDatatype ? BuiltinFunction.DtRank : BuiltinFunction.BoxRank, null, e1));

        default:
          Contract.Assert(false); throw new Cce.UnreachableException();  // unexpected binary expression
      }
      liftLit = liftLit && !keepLits;
      var ae0 = keepLits ? oe0 : e0;
      var ae1 = keepLits ? oe1 : e1;
      Expr re = Expr.Binary(GetToken(binaryExpr), bOpcode, ae0, ae1);
      if (liftLit) {
        re = MaybeLit(re, typ);
      }
      return re;
    }

    /// <summary>
    /// Translate like 0 < s[Box(elmt)], but try to avoid as many set functions as possible in the
    /// translation, because such functions can mess up triggering.
    /// Note: This method must be kept in synch with RewriteInExpr.
    /// </summary>
    public Expr TrInMultiSet(IOrigin tok, Expr elmt, Expression s, Type elmtType, bool aggressive) {
      Contract.Requires(tok != null);
      Contract.Requires(elmt != null);
      Contract.Requires(s != null);
      Contract.Requires(elmtType != null);

      Contract.Ensures(Contract.Result<Expr>() != null);
      var elmtBox = BoxIfNecessary(tok, elmt, elmtType);
      return TrInMultiSet_Aux(tok, elmt, elmtBox, s, aggressive);
    }

    public Expr TrInMultiSet_Aux(IOrigin tok, Expr elmt, Expr elmtBox, Expression s, bool aggressive) {
      Contract.Requires(tok != null);
      Contract.Requires(elmt != null);
      Contract.Requires(s != null);
      Contract.Requires(elmtBox != null);

      Contract.Ensures(Contract.Result<Expr>() != null);

      s = s.Resolved;
      if (s is BinaryExpr && aggressive) {
        BinaryExpr bin = (BinaryExpr)s;
        switch (bin.ResolvedOp) {
          case BinaryExpr.ResolvedOpcode.MultiSetUnion:
            return Expr.Binary(tok, BinaryOperator.Opcode.Or, TrInMultiSet_Aux(tok, elmt, elmtBox, bin.E0, aggressive), TrInMultiSet_Aux(tok, elmt, elmtBox, bin.E1, aggressive));
          case BinaryExpr.ResolvedOpcode.MultiSetIntersection:
            return Expr.Binary(tok, BinaryOperator.Opcode.And, TrInMultiSet_Aux(tok, elmt, elmtBox, bin.E0, aggressive), TrInMultiSet_Aux(tok, elmt, elmtBox, bin.E1, aggressive));
          default:
            break;
        }
      } else if (s is MultiSetDisplayExpr) {
        MultiSetDisplayExpr disp = (MultiSetDisplayExpr)s;
        Expr disjunction = null;
        foreach (Expression a in disp.Elements) {
          Expr disjunct = Expr.Eq(elmt, TrExpr(a));
          if (disjunction == null) {
            disjunction = disjunct;
          } else {
            disjunction = BplOr(disjunction, disjunct);
          }
        }
        if (disjunction == null) {
          return Expr.False;
        } else {
          return disjunction;
        }
      }
      var result = Expr.Gt(BoogieGenerator.MultisetMultiplicity(tok, TrExpr(s), elmtBox), Expr.Literal(0));
      result.tok = tok;
      return result;
    }


    /// <summary>
    /// Translate like s[Box(elmt)], but try to avoid as many set functions as possible in the
    /// translation, because such functions can mess up triggering.
    /// </summary>
    public Expr TrInSet(IOrigin tok, Expr elmt, Expression s, Type elmtType, bool isFiniteSet, bool aggressive, out bool performedRewrite) {
      Contract.Requires(tok != null);
      Contract.Requires(elmt != null);
      Contract.Requires(s != null);
      Contract.Requires(elmtType != null);
      Contract.Ensures(Contract.Result<Expr>() != null);

      var elmtBox = BoxIfNecessary(tok, elmt, elmtType);
      var r = TrInSet_Aux(tok, elmt, elmtBox, s, isFiniteSet, aggressive, out performedRewrite);
      Contract.Assert(performedRewrite == RewriteInExpr(s, aggressive)); // sanity check
      return r;
    }
    /// <summary>
    /// The worker routine for TrInSet.  This method takes both "elmt" and "elmtBox" as parameters,
    /// using the former when the unboxed form is needed and the latter when the boxed form is needed.
    /// This gives the caller the flexibility to pass in either "o, Box(o)" or "Unbox(bx), bx".
    /// Note: This method must be kept in synch with RewriteInExpr.
    /// </summary>
    public Expr TrInSet_Aux(IOrigin tok, Expr elmt, Expr elmtBox, Expression s, bool isFiniteSet, bool aggressive,
      out bool performedRewrite, Func<Expr, Expr> extractObjectFromMemoryLocation = null) {
      Contract.Requires(tok != null);
      Contract.Requires(elmt != null);
      Contract.Requires(elmtBox != null);
      Contract.Requires(s != null);
      Contract.Ensures(Contract.Result<Expr>() != null);

      performedRewrite = true;  // assume a rewrite will happen
      s = s.Resolved;
      bool pr;
      if (s is BinaryExpr && aggressive) {
        BinaryExpr bin = (BinaryExpr)s;
        switch (bin.ResolvedOp) {
          case BinaryExpr.ResolvedOpcode.Union:
            return BplOr(
              TrInSet_Aux(tok, elmt, elmtBox, bin.E0, isFiniteSet, aggressive, out pr, extractObjectFromMemoryLocation),
              TrInSet_Aux(tok, elmt, elmtBox, bin.E1, isFiniteSet, aggressive, out pr, extractObjectFromMemoryLocation));
          case BinaryExpr.ResolvedOpcode.Intersection:
            return BplAnd(
              TrInSet_Aux(tok, elmt, elmtBox, bin.E0, isFiniteSet, aggressive, out pr, extractObjectFromMemoryLocation),
              TrInSet_Aux(tok, elmt, elmtBox, bin.E1, isFiniteSet, aggressive, out pr, extractObjectFromMemoryLocation));
          case BinaryExpr.ResolvedOpcode.SetDifference:
            return BplAnd(
              TrInSet_Aux(tok, elmt, elmtBox, bin.E0, isFiniteSet, aggressive, out pr, extractObjectFromMemoryLocation),
              Expr.Not(TrInSet_Aux(tok, elmt, elmtBox, bin.E1, isFiniteSet, aggressive, out pr, extractObjectFromMemoryLocation)));
          default:
            break;
        }
      } else if (s is SetDisplayExpr) {
        SetDisplayExpr disp = (SetDisplayExpr)s;
        Expr disjunction = null;
        foreach (Expression a in disp.Elements) {
          var oneElem = TrExpr(a);
          oneElem = extractObjectFromMemoryLocation != null ? extractObjectFromMemoryLocation(oneElem) : oneElem;
          Expr disjunct = Expr.Eq(elmt, oneElem);
          if (disjunction == null) {
            disjunction = disjunct;
          } else {
            disjunction = BplOr(disjunction, disjunct);
          }
        }
        if (disjunction == null) {
          return Expr.False;
        } else {
          return disjunction;
        }
      } else if (s is SetComprehension) {
        var compr = (SetComprehension)s;
        // Translate "elmt in set xs | R :: T[xs]" into:
        //     exists xs :: CorrectType(xs) && R && elmt==T[xs]
        // or if "T[xs]" is "xs", then:
        //     CorrectType(elmt) && R[xs := elmt]
        if (compr.TermIsSimple && extractObjectFromMemoryLocation == null) {
          // CorrectType(elmt) && R[xs := elmt]
          // Note, we can always use NOALLOC here.
          Expr typeAntecedent = BoogieGenerator.GetWhereClause(GetToken(compr), elmt, compr.BoundVars[0].Type, this, NOALLOC) ?? Expr.True;
          var range = Substitute(compr.Range, compr.BoundVars[0], new BoogieWrapper(elmt, compr.BoundVars[0].Type));
          return BplAnd(typeAntecedent, TrExpr(range));
        } else {
          // exists xs :: CorrectType(xs) && R && elmt==T[xs]
          List<bool> freeOfAlloc = BoundedPool.HasBounds(compr.Bounds, BoundedPool.PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc);
          var bvars = new List<Variable>();
          Expr typeAntecedent = TrBoundVariables(compr.BoundVars, bvars, false, freeOfAlloc) ?? Expr.True;
          var eq = Expr.Eq(elmtBox, BoxIfNecessary(GetToken(compr), extractObjectFromMemoryLocation != null ? extractObjectFromMemoryLocation(TrExpr(compr.Term)) : TrExpr(compr.Term), compr.Term.Type));
          var ebody = BplAnd(BplAnd(typeAntecedent, TrExpr(compr.Range)), eq);
          var triggers = BoogieGenerator.TrTrigger(this, compr.Attributes, GetToken(compr));
          return new Boogie.ExistsExpr(GetToken(compr), bvars, triggers, ebody);
        }
      }

      if (extractObjectFromMemoryLocation != null) {
        // Translate "elmt in s" into "exists xs :: xs in s && elem == xs.0"
        // with extractObjectFromMemoryLocation = (xs) => xs.0
        var xs = new BoundVariable(GetToken(s), new TypedIdent(tok, "xs", BoogieGenerator.TrType(s.Type.AsSetType.Arg)));
        var xsExpr = new Boogie.IdentifierExpr(xs.tok, xs);
        var xsExprBoxExtract = extractObjectFromMemoryLocation(xsExpr);
        // Create the trigger Set#IsMember(xs, s)
        var trigger = new Trigger(tok, false, [
          BoogieGenerator.FunctionCall(tok, BuiltinFunction.SetIsMember, Boogie.Type.Bool, xsExpr, TrExpr(s))
        ]);
        var ebody = Expr.Eq(elmt, xsExprBoxExtract);
        return new Boogie.ExistsExpr(GetToken(s), new List<Variable>() { xs }, trigger, ebody);
      }
      performedRewrite = false;

      return BoogieGenerator.IsSetMember(tok, TrExpr(s), elmtBox, isFiniteSet);
    }

    /// <summary>
    /// This method returns "true" iff TrInSet_Aux/TrInMultiSet_Aux will rewrite an expression "x in s".
    /// Note: This method must be kept in synch with TrInSet_Aux/TrInMultiSet_Aux.
    /// </summary>
    public static bool RewriteInExpr(Expression s, bool aggressive) {
      Contract.Requires(s != null);

      s = s.Resolved;
      if (s is BinaryExpr && aggressive) {
        BinaryExpr bin = (BinaryExpr)s;
        switch (bin.ResolvedOp) {
          case BinaryExpr.ResolvedOpcode.Union:
          case BinaryExpr.ResolvedOpcode.Intersection:
          case BinaryExpr.ResolvedOpcode.SetDifference:
          case BinaryExpr.ResolvedOpcode.MultiSetUnion:
          case BinaryExpr.ResolvedOpcode.MultiSetIntersection:
            return true;
          default:
            break;
        }
      } else if (s is SetDisplayExpr || s is MultiSetDisplayExpr) {
        return true;
      } else if (s is SetComprehension) {
        return true;
      }
      return false;
    }


    private Expr BinaryExprCanCallAssumption(BinaryExpr expr, CanCallOptions cco) {
      // The short-circuiting boolean operators &&, ||, and ==> end up duplicating their
      // left argument. Therefore, we first try to re-associate the expression to make
      // left arguments smaller.
      var newExpr = ReAssociateToTheRight(ref expr);
      if (newExpr != null) {
        return CanCallAssumption(newExpr, cco);
      }

      var t0 = CanCallAssumption(expr.E0, cco);
      var t1 = CanCallAssumption(expr.E1, cco);
      switch (expr.ResolvedOp) {
        case BinaryExpr.ResolvedOpcode.And:
        case BinaryExpr.ResolvedOpcode.Imp:
          t1 = BplImp(TrExpr(expr.E0), t1);
          break;
        case BinaryExpr.ResolvedOpcode.Or:
          t1 = BplImp(Expr.Not(TrExpr(expr.E0)), t1);
          break;
        case BinaryExpr.ResolvedOpcode.EqCommon:
        case BinaryExpr.ResolvedOpcode.NeqCommon: {
            Expr r = Expr.True;
            if (cco is not { SkipIsA: true }) {
              if (expr.E0 is { Type: { AsDatatype: { } dt0 }, Resolved: not DatatypeValue }) {
                var funcId = new FunctionCall(new Boogie.IdentifierExpr(expr.Origin, "$IsA#" + dt0.FullSanitizedName, Boogie.Type.Bool));
                r = BplAnd(r, new NAryExpr(expr.Origin, funcId, new List<Expr> { TrExpr(expr.E0) }));
              }
              if (expr.E1 is { Type: { AsDatatype: { } dt1 }, Resolved: not DatatypeValue }) {
                var funcId = new FunctionCall(new Boogie.IdentifierExpr(expr.Origin, "$IsA#" + dt1.FullSanitizedName, Boogie.Type.Bool));
                r = BplAnd(r, new NAryExpr(expr.Origin, funcId, new List<Expr> { TrExpr(expr.E1) }));
              }
            }
            return BplAnd(r, BplAnd(t0, t1));
          }
        case BinaryExpr.ResolvedOpcode.Mul:
          if (7 <= BoogieGenerator.options.ArithMode) {
            if (expr.E0.Type.IsNumericBased(Type.NumericPersuasion.Int) && !BoogieGenerator.DisableNonLinearArithmetic) {
              // Produce a useful fact about the associativity of multiplication. It is a bit dicey to do as an axiom.
              // Change (k*A)*B or (A*k)*B into (A*B)*k, where k is a numeric literal
              if (expr.E0.Resolved is BinaryExpr left && left.ResolvedOp == BinaryExpr.ResolvedOpcode.Mul) {
                Expr r = Expr.True;
                if (left.E0.Resolved is LiteralExpr) {
                  // (K*A)*B == (A*B)*k
                  var y = Expression.CreateMul(Expression.CreateMul(left.E1, expr.E1), left.E0);
                  var eq = Expression.CreateEq(expr, y, expr.E0.Type);
                  r = BplAnd(r, TrExpr(eq));
                }
                if (left.E1.Resolved is LiteralExpr) {
                  // (A*k)*B == (A*B)*k
                  var y = Expression.CreateMul(Expression.CreateMul(left.E0, expr.E1), left.E1);
                  var eq = Expression.CreateEq(expr, y, expr.E0.Type);
                  r = BplAnd(r, TrExpr(eq));
                }
                if (r != Expr.True) {
                  return BplAnd(BplAnd(t0, t1), r);
                }
              }
            }
          }
          break;
      }
      return BplAnd(t0, t1);
    }

    /// <summary>
    /// If "expr" is a binary boolean operation, then try to re-associate it to make the left argument smaller.
    /// If it is possible, then "true" is returned and "expr" returns as the re-associated expression (no boolean simplifications are performed).
    /// If not, then "false" is returned and "expr" is unchanged.
    /// </summary>
    Expression ReAssociateToTheRight(ref BinaryExpr top) {
      if (Expression.StripParens(top.E0) is BinaryExpr left) {
        // We have an expression of the form "(A oo B) pp C"
        var A = left.E0;
        var oo = left.ResolvedOp;
        var B = left.E1;
        var pp = top.ResolvedOp;
        var C = top.E1;

        if (oo == BinaryExpr.ResolvedOpcode.And && pp == BinaryExpr.ResolvedOpcode.And) {
          // rewrite    (A && B) && C    into    A && (B && C)
          return Expression.CreateAnd(A, Expression.CreateAnd(B, C, false), false);
        }

        if (oo == BinaryExpr.ResolvedOpcode.And && pp == BinaryExpr.ResolvedOpcode.Imp) {
          // rewrite    (A && B) ==> C    into    A ==> (B ==> C)
          return Expression.CreateImplies(A, Expression.CreateImplies(B, C, false), false);
        }

        if (oo == BinaryExpr.ResolvedOpcode.Or && pp == BinaryExpr.ResolvedOpcode.Or) {
          // rewrite    (A || B) || C    into    A || (B || C)
          return Expression.CreateOr(A, Expression.CreateOr(B, C, false), false);
        }

        if (oo == BinaryExpr.ResolvedOpcode.Imp && pp == BinaryExpr.ResolvedOpcode.Or) {
          // rewrite    (A ==> B) || C    into    A ==> (B || C)
          return Expression.CreateImplies(A, Expression.CreateOr(B, C, false), false);
        }
      }
      return null;
    }
  }
}