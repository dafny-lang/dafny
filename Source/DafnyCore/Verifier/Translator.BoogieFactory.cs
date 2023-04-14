
using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using Bpl = Microsoft.Boogie;
using static Microsoft.Dafny.Util;

namespace Microsoft.Dafny {
  partial class Translator {
    public Bpl.Type BplBvType(int width) {
      Contract.Requires(0 <= width);
      if (width == 0) {
        // Boogie claims to support bv0, but it translates it straight down to the SMT solver's 0-width bitvector type.
        // However, the SMT-LIB 2 standard does not define such a bitvector width, so this is a bug in Boogie.  The
        // best would be to fix this in Boogie, but for now, we simply work around it here.
        return predef.Bv0Type;
      } else {
        return Bpl.Type.GetBvType(width);
      }
    }

    internal Bpl.Expr BplBvLiteralExpr(Bpl.IToken tok, BaseTypes.BigNum n, BitvectorType bitvectorType) {
      Contract.Requires(tok != null);
      Contract.Requires(bitvectorType != null);
      return BplBvLiteralExpr(tok, n, bitvectorType.Width);
    }
    internal Bpl.Expr BplBvLiteralExpr(Bpl.IToken tok, BaseTypes.BigNum n, int width) {
      Contract.Requires(tok != null);
      Contract.Requires(0 <= width);
      if (width == 0) {
        // see comment in BplBvType
        Contract.Assert(n.IsZero);
        return Bpl.Expr.Literal(0);
      } else if (n.IsNegative) {
        // This can only happen if some error is reported elsewhere. Nevertheless, we do need to
        // generate a Boogie expression and Boogie would crash if we pass a negative number to
        // Bpl.LiteralExpr for a bitvector.
        var zero = new Bpl.LiteralExpr(tok, BaseTypes.BigNum.ZERO, width);
        var absN = new Bpl.LiteralExpr(tok, -n, width);
        var etran = new ExpressionTranslator(this, predef, tok);
        return etran.TrToFunctionCall(tok, "sub_bv" + width, BplBvType(width), zero, absN, false);
      } else {
        return new Bpl.LiteralExpr(tok, n, width);
      }
    }

    enum BuiltinFunction {
      Lit,
      LitInt,
      LitReal,
      LayerSucc,
      AsFuelBottom,
      CharFromInt,
      CharToInt,
      IsChar,

      Is, IsBox,
      IsAlloc, IsAllocBox,

      IsTraitParent,

      SetCard,
      SetEmpty,
      SetUnionOne,
      SetUnion,
      SetIntersection,
      SetDifference,
      SetEqual,
      SetSubset,
      SetDisjoint,

      ISetEmpty,
      ISetUnionOne,
      ISetUnion,
      ISetIntersection,
      ISetDifference,
      ISetEqual,
      ISetSubset,
      ISetDisjoint,

      MultiSetCard,
      MultiSetEmpty,
      MultiSetUnionOne,
      MultiSetUnion,
      MultiSetIntersection,
      MultiSetDifference,
      MultiSetEqual,
      MultiSetSubset,
      MultiSetDisjoint,
      MultiSetFromSet,
      MultiSetFromSeq,
      IsGoodMultiSet,

      SeqLength,
      SeqEmpty,
      SeqBuild,
      SeqAppend,
      SeqIndex,
      SeqUpdate,
      SeqContains,
      SeqDrop,
      SeqTake,
      SeqEqual,
      SeqSameUntil,
      SeqFromArray,
      SeqRank,

      MapEmpty,
      MapCard,
      MapDomain,
      MapElements,
      MapEqual,
      MapDisjoint,
      MapUnion,
      MapGlue,

      IMapEmpty,
      IMapDomain,
      IMapElements,
      IMapEqual,
      IMapGlue,

      IndexField,
      MultiIndexField,

      Box,
      Unbox,

      RealToInt,
      IntToReal,

      IsGoodHeap,
      IsHeapAnchor,
      HeapSucc,
      HeapSuccGhost,

      DynamicType,  // allocated type (of object reference)
      TypeTuple,
      DeclType,
      FieldOfDecl,
      FDim,  // field dimension (0 - named, 1 or more - indexed)
      IsGhostField,

      DatatypeCtorId,
      DtRank,
      BoxRank,

      GenericAlloc,

      AtLayer
    }

    Bpl.Expr Lit(Bpl.Expr expr, Bpl.Type typ) {
      Contract.Requires(expr != null);
      Contract.Requires(typ != null);
      // To avoid Boogie's int_2_U and U_2_int conversions, which seem to cause problems with
      // arithmetic reasoning, we use several Lit functions.  In particular, we use one for
      // integers, one for reals, and one for everything else.
      if (typ.IsInt) {
        return FunctionCall(expr.tok, BuiltinFunction.LitInt, null, expr);
      } else if (typ.IsReal) {
        return FunctionCall(expr.tok, BuiltinFunction.LitReal, null, expr);
      } else {
        return FunctionCall(expr.tok, BuiltinFunction.Lit, typ, expr);
      }
    }

    Bpl.Expr Lit(Bpl.Expr expr) {
      return Lit(expr, expr.Type);
    }

    private static Bpl.Expr GetLit(Bpl.Expr expr) {
      if (expr is Bpl.NAryExpr) {
        Bpl.NAryExpr app = (Bpl.NAryExpr)expr;
        switch (app.Fun.FunctionName) {
          case "LitInt":
          case "LitReal":
          case "Lit":
            return app.Args[0];
          default:
            break;
        }
      }
      return null;
    }

    public static Bpl.AssumeCmd TrAssumeCmd(Bpl.IToken tok, Bpl.Expr expr, Bpl.QKeyValue attributes = null) {
      var litArgument = GetLit(expr);
      if (litArgument is Bpl.LiteralExpr literalExpr && literalExpr.asBool) {
        // In most cases, we leave any Lit brackets that "expr" may have. In the past, these brackets
        // had always been removed here. Alas, some brittle test cases stopped verifying if we
        // keep "assume Lit(true)" instead of simplifying it to "assume true". Therefore, as a
        // special case, we remove the Lit brackets from the literal "true".
        expr = litArgument;
      }
      return attributes == null ? new Bpl.AssumeCmd(tok, expr) : new Bpl.AssumeCmd(tok, expr, attributes);
    }

    static Bpl.Expr RemoveLit(Bpl.Expr expr) {
      return GetLit(expr) ?? expr;
    }

    readonly ISet<string> letBoundVariablesWithLitRHS = new HashSet<string>();

    bool IsLit(Bpl.Expr expr) {
      if (expr is Bpl.IdentifierExpr ie) {
        return letBoundVariablesWithLitRHS.Contains(ie.Name);
      }
      return GetLit(expr) != null;
    }

    // The "typeInstantiation" argument is passed in to help construct the result type of the function.
    Bpl.NAryExpr FunctionCall(Bpl.IToken tok, BuiltinFunction f, Bpl.Type typeInstantiation, params Bpl.Expr[] args) {
      Contract.Requires(tok != null);
      Contract.Requires(args != null);
      Contract.Requires(predef != null);
      Contract.Ensures(Contract.Result<Bpl.NAryExpr>() != null);

      switch (f) {
        case BuiltinFunction.LitInt:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "LitInt", Bpl.Type.Int, args);
        case BuiltinFunction.LitReal:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "LitReal", Bpl.Type.Real, args);
        case BuiltinFunction.Lit:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "Lit", typeInstantiation, args);
        case BuiltinFunction.LayerSucc:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "$LS", predef.LayerType, args);
        case BuiltinFunction.AsFuelBottom:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "AsFuelBottom", predef.LayerType, args);
        case BuiltinFunction.CharFromInt:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "char#FromInt", predef.CharType, args);
        case BuiltinFunction.CharToInt:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "char#ToInt", predef.CharType, args);
        case BuiltinFunction.IsChar:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "char#IsChar", Bpl.Type.Bool, args);

        case BuiltinFunction.Is:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "$Is", Bpl.Type.Bool, args);
        case BuiltinFunction.IsBox:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "$IsBox", Bpl.Type.Bool, args);
        case BuiltinFunction.IsAlloc:
          Contract.Assert(args.Length == 3);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "$IsAlloc", Bpl.Type.Bool, args);
        case BuiltinFunction.IsAllocBox:
          Contract.Assert(args.Length == 3);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "$IsAllocBox", Bpl.Type.Bool, args);

        case BuiltinFunction.IsTraitParent:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "IsTraitParent", Bpl.Type.Bool, args);

        case BuiltinFunction.SetCard:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "Set#Card", Bpl.Type.Int, args);
        case BuiltinFunction.SetEmpty: {
            Contract.Assert(args.Length == 0);
            Contract.Assert(typeInstantiation != null);
            Bpl.Type resultType = predef.SetType(tok, true, typeInstantiation);
            return Bpl.Expr.CoerceType(tok, FunctionCall(tok, "Set#Empty", resultType, args), resultType);
          }
        case BuiltinFunction.SetUnionOne:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "Set#UnionOne", predef.SetType(tok, true, typeInstantiation), args);
        case BuiltinFunction.SetUnion:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "Set#Union", predef.SetType(tok, true, typeInstantiation), args);
        case BuiltinFunction.SetIntersection:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "Set#Intersection", predef.SetType(tok, true, typeInstantiation), args);
        case BuiltinFunction.SetDifference:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "Set#Difference", predef.SetType(tok, true, typeInstantiation), args);
        case BuiltinFunction.SetEqual:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "Set#Equal", Bpl.Type.Bool, args);
        case BuiltinFunction.SetSubset:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "Set#Subset", Bpl.Type.Bool, args);
        case BuiltinFunction.SetDisjoint:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "Set#Disjoint", Bpl.Type.Bool, args);
        case BuiltinFunction.ISetEmpty: {
            Contract.Assert(args.Length == 0);
            Contract.Assert(typeInstantiation != null);
            Bpl.Type resultType = predef.SetType(tok, false, typeInstantiation);
            return Bpl.Expr.CoerceType(tok, FunctionCall(tok, "ISet#Empty", resultType, args), resultType);
          }
        case BuiltinFunction.ISetUnionOne:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "ISet#UnionOne", predef.SetType(tok, false, typeInstantiation), args);
        case BuiltinFunction.ISetUnion:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "ISet#Union", predef.SetType(tok, false, typeInstantiation), args);
        case BuiltinFunction.ISetIntersection:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "ISet#Intersection", predef.SetType(tok, false, typeInstantiation), args);
        case BuiltinFunction.ISetDifference:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "ISet#Difference", predef.SetType(tok, false, typeInstantiation), args);
        case BuiltinFunction.ISetEqual:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "ISet#Equal", Bpl.Type.Bool, args);
        case BuiltinFunction.ISetSubset:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "ISet#Subset", Bpl.Type.Bool, args);
        case BuiltinFunction.ISetDisjoint:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "ISet#Disjoint", Bpl.Type.Bool, args);
        case BuiltinFunction.MultiSetCard:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "MultiSet#Card", Bpl.Type.Int, args);
        case BuiltinFunction.MultiSetEmpty: {
            Contract.Assert(args.Length == 0);
            Contract.Assert(typeInstantiation != null);
            Bpl.Type resultType = predef.MultiSetType(tok, typeInstantiation);
            return Bpl.Expr.CoerceType(tok, FunctionCall(tok, "MultiSet#Empty", resultType, args), resultType);
          }
        case BuiltinFunction.MultiSetUnionOne:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "MultiSet#UnionOne", predef.MultiSetType(tok, typeInstantiation), args);
        case BuiltinFunction.MultiSetUnion:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "MultiSet#Union", predef.MultiSetType(tok, typeInstantiation), args);
        case BuiltinFunction.MultiSetIntersection:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "MultiSet#Intersection", predef.MultiSetType(tok, typeInstantiation), args);
        case BuiltinFunction.MultiSetDifference:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "MultiSet#Difference", predef.MultiSetType(tok, typeInstantiation), args);
        case BuiltinFunction.MultiSetEqual:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "MultiSet#Equal", Bpl.Type.Bool, args);
        case BuiltinFunction.MultiSetSubset:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "MultiSet#Subset", Bpl.Type.Bool, args);
        case BuiltinFunction.MultiSetDisjoint:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "MultiSet#Disjoint", Bpl.Type.Bool, args);
        case BuiltinFunction.MultiSetFromSet:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "MultiSet#FromSet", predef.MultiSetType(tok, typeInstantiation), args);
        case BuiltinFunction.MultiSetFromSeq:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "MultiSet#FromSeq", predef.MultiSetType(tok, typeInstantiation), args);
        case BuiltinFunction.IsGoodMultiSet:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "$IsGoodMultiSet", Bpl.Type.Bool, args);

        case BuiltinFunction.SeqLength:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "Seq#Length", Bpl.Type.Int, args);
        case BuiltinFunction.SeqEmpty: {
            Contract.Assert(args.Length == 0);
            Contract.Assert(typeInstantiation != null);
            Bpl.Type resultType = predef.SeqType(tok, typeInstantiation);
            return Bpl.Expr.CoerceType(tok, FunctionCall(tok, "Seq#Empty", resultType, args), resultType);
          }
        case BuiltinFunction.SeqBuild:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "Seq#Build", predef.SeqType(tok, typeInstantiation), args);
        case BuiltinFunction.SeqAppend:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "Seq#Append", predef.SeqType(tok, typeInstantiation), args);
        case BuiltinFunction.SeqIndex:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "Seq#Index", typeInstantiation, args);
        case BuiltinFunction.SeqUpdate:
          Contract.Assert(args.Length == 3);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "Seq#Update", predef.SeqType(tok, typeInstantiation), args);
        case BuiltinFunction.SeqContains:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "Seq#Contains", Bpl.Type.Bool, args);
        case BuiltinFunction.SeqDrop:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "Seq#Drop", predef.SeqType(tok, typeInstantiation), args);
        case BuiltinFunction.SeqTake:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "Seq#Take", predef.SeqType(tok, typeInstantiation), args);
        case BuiltinFunction.SeqEqual:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "Seq#Equal", Bpl.Type.Bool, args);
        case BuiltinFunction.SeqSameUntil:
          Contract.Assert(args.Length == 3);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "Seq#SameUntil", Bpl.Type.Bool, args);
        case BuiltinFunction.SeqFromArray:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "Seq#FromArray", typeInstantiation, args);
        case BuiltinFunction.SeqRank:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "Seq#Rank", Bpl.Type.Int, args);

        case BuiltinFunction.MapEmpty: {
            Contract.Assert(args.Length == 0);
            Contract.Assert(typeInstantiation != null);
            Bpl.Type resultType = predef.MapType(tok, true, typeInstantiation, typeInstantiation);  // use 'typeInstantiation' (which is really always just BoxType anyway) as both type arguments
            return Bpl.Expr.CoerceType(tok, FunctionCall(tok, "Map#Empty", resultType, args), resultType);
          }
        case BuiltinFunction.MapCard:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "Map#Card", Bpl.Type.Int, args);
        case BuiltinFunction.MapDomain:
          Contract.Assert(args.Length == 1);
          return FunctionCall(tok, "Map#Domain", typeInstantiation, args);
        case BuiltinFunction.MapElements:
          Contract.Assert(args.Length == 1);
          return FunctionCall(tok, "Map#Elements", typeInstantiation, args);
        case BuiltinFunction.MapGlue:
          Contract.Assert(args.Length == 3);
          return FunctionCall(tok, "Map#Glue", predef.MapType(tok, true, predef.BoxType, predef.BoxType), args);
        case BuiltinFunction.MapEqual:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "Map#Equal", Bpl.Type.Bool, args);
        case BuiltinFunction.MapDisjoint:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "Map#Disjoint", Bpl.Type.Bool, args);
        case BuiltinFunction.MapUnion:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "Map#Disjoint", typeInstantiation, args);

        case BuiltinFunction.IMapEmpty: {
            Contract.Assert(args.Length == 0);
            Contract.Assert(typeInstantiation != null);
            Bpl.Type resultType = predef.MapType(tok, false, typeInstantiation, typeInstantiation);  // use 'typeInstantiation' (which is really always just BoxType anyway) as both type arguments
            return Bpl.Expr.CoerceType(tok, FunctionCall(tok, "IMap#Empty", resultType, args), resultType);
          }
        case BuiltinFunction.IMapDomain:
          Contract.Assert(args.Length == 1);
          return FunctionCall(tok, "IMap#Domain", typeInstantiation, args);
        case BuiltinFunction.IMapElements:
          Contract.Assert(args.Length == 1);
          return FunctionCall(tok, "IMap#Elements", typeInstantiation, args);
        case BuiltinFunction.IMapGlue:
          Contract.Assert(args.Length == 3);
          return FunctionCall(tok, "IMap#Glue", predef.MapType(tok, false, predef.BoxType, predef.BoxType), args);
        case BuiltinFunction.IMapEqual:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "IMap#Equal", Bpl.Type.Bool, args);

        case BuiltinFunction.IndexField:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "IndexField", predef.FieldName(tok, predef.BoxType), args);
        case BuiltinFunction.MultiIndexField:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "MultiIndexField", predef.FieldName(tok, predef.BoxType), args);

        case BuiltinFunction.Box:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "$Box", predef.BoxType, args);
        case BuiltinFunction.Unbox:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation != null);
          return Bpl.Expr.CoerceType(tok, FunctionCall(tok, "$Unbox", typeInstantiation, args), typeInstantiation);

        case BuiltinFunction.RealToInt:
          Contract.Assume(args.Length == 1);
          Contract.Assume(typeInstantiation == null);
          return FunctionCall(tok, "Int", Bpl.Type.Int, args);
        case BuiltinFunction.IntToReal:
          Contract.Assume(args.Length == 1);
          Contract.Assume(typeInstantiation == null);
          return FunctionCall(tok, "Real", Bpl.Type.Real, args);

        case BuiltinFunction.IsGoodHeap:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "$IsGoodHeap", Bpl.Type.Bool, args);
        case BuiltinFunction.IsHeapAnchor:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "$IsHeapAnchor", Bpl.Type.Bool, args);
        case BuiltinFunction.HeapSucc:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "$HeapSucc", Bpl.Type.Bool, args);
        case BuiltinFunction.HeapSuccGhost:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "$HeapSuccGhost", Bpl.Type.Bool, args);

        case BuiltinFunction.DynamicType:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "dtype", predef.ClassNameType, args);
        case BuiltinFunction.TypeTuple:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "TypeTuple", predef.ClassNameType, args);
        case BuiltinFunction.DeclType:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "DeclType", predef.ClassNameType, args);
        case BuiltinFunction.FieldOfDecl:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "FieldOfDecl", predef.FieldName(tok, typeInstantiation), args);
        case BuiltinFunction.FDim:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "FDim", Bpl.Type.Int, args);
        case BuiltinFunction.IsGhostField:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "$IsGhostField", Bpl.Type.Bool, args);

        case BuiltinFunction.DatatypeCtorId:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "DatatypeCtorId", predef.DtCtorId, args);
        case BuiltinFunction.DtRank:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "DtRank", Bpl.Type.Int, args);
        case BuiltinFunction.BoxRank:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "BoxRank", Bpl.Type.Int, args);

        case BuiltinFunction.GenericAlloc:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "GenericAlloc", Bpl.Type.Bool, args);

        case BuiltinFunction.AtLayer:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "AtLayer", typeInstantiation, args);

        default:
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected built-in function
      }
    }

    static Bpl.NAryExpr FunctionCall(Bpl.IToken tok, string function, Bpl.Type returnType, params Bpl.Expr[] args) {
      Contract.Requires(tok != null);
      Contract.Requires(function != null);
      Contract.Requires(returnType != null);
      Contract.Requires(args != null);
      Contract.Ensures(Contract.Result<Bpl.NAryExpr>() != null);

      return new Bpl.NAryExpr(tok, new Bpl.FunctionCall(new Bpl.IdentifierExpr(tok, function, returnType)), new List<Bpl.Expr>(args));
    }

    static Bpl.NAryExpr FunctionCall(Bpl.IToken tok, string function, Bpl.Type returnType, List<Bpl.Expr> args) {
      Contract.Requires(tok != null);
      Contract.Requires(function != null);
      Contract.Requires(returnType != null);
      Contract.Requires(cce.NonNullElements(args));
      Contract.Ensures(Contract.Result<Bpl.NAryExpr>() != null);

      List<Bpl.Expr> aa = new List<Bpl.Expr>();
      foreach (Bpl.Expr arg in args) {
        aa.Add(arg);
      }
      return new Bpl.NAryExpr(tok, new Bpl.FunctionCall(new Bpl.IdentifierExpr(tok, function, returnType)), aa);
    }

    public Bpl.Expr ProperSubset(Bpl.IToken tok, Bpl.Expr e0, Bpl.Expr e1) {
      Contract.Requires(tok != null);
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      return Bpl.Expr.Binary(tok, Bpl.BinaryOperator.Opcode.And,
        FunctionCall(tok, BuiltinFunction.SetSubset, null, e0, e1),
        Bpl.Expr.Not(FunctionCall(tok, BuiltinFunction.SetSubset, null, e1, e0)));
    }
    public Bpl.Expr ProperMultiset(Bpl.IToken tok, Bpl.Expr e0, Bpl.Expr e1) {
      Contract.Requires(tok != null);
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      return Bpl.Expr.Binary(tok, Bpl.BinaryOperator.Opcode.And,
        FunctionCall(tok, BuiltinFunction.MultiSetSubset, null, e0, e1),
        Bpl.Expr.Not(FunctionCall(tok, BuiltinFunction.MultiSetEqual, null, e0, e1)));
    }
    public Bpl.Expr ProperPrefix(Bpl.IToken tok, Bpl.Expr e0, Bpl.Expr e1) {
      Contract.Requires(tok != null);
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);
      Bpl.Expr len0 = FunctionCall(tok, BuiltinFunction.SeqLength, null, e0);
      Bpl.Expr len1 = FunctionCall(tok, BuiltinFunction.SeqLength, null, e1);
      var result = Bpl.Expr.And(
        Bpl.Expr.Lt(len0, len1),
        FunctionCall(tok, BuiltinFunction.SeqSameUntil, null, e0, e1, len0));
      result.tok = tok;
      return result;
    }

    Bpl.Expr ArrayLength(Bpl.IToken tok, Bpl.Expr arr, int totalDims, int dim) {
      Contract.Requires(tok != null);
      Contract.Requires(arr != null);
      Contract.Requires(1 <= totalDims);
      Contract.Requires(0 <= dim && dim < totalDims);

      string name = "_System." + BuiltIns.ArrayClassName(totalDims) + ".Length";
      if (totalDims != 1) {
        name += dim;
      }
      return new Bpl.NAryExpr(tok, new Bpl.FunctionCall(new Bpl.IdentifierExpr(tok, name, Bpl.Type.Int)), new List<Bpl.Expr> { arr });
    }

    static Bpl.Expr BplForall(IEnumerable<Bpl.Variable> args_in, Bpl.Expr body) {
      Contract.Requires(args_in != null);
      Contract.Requires(body != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);
      var args = new List<Bpl.Variable>(args_in);
      if (args.Count == 0) {
        return body;
      } else {
        return new Bpl.ForallExpr(body.tok, args, body); // NO_TRIGGER
      }
    }

    // Note: if the trigger is null, makes a forall without any triggers
    static Bpl.Expr BplForall(IEnumerable<Bpl.Variable> args_in, Bpl.Trigger trg, Bpl.Expr body) {
      if (trg == null) {
        return BplForall(args_in, body); // NO_TRIGGER
      } else {
        var args = new List<Bpl.Variable>(args_in);
        if (args.Count == 0) {
          return body;
        } else {
          return new Bpl.ForallExpr(body.tok, args, trg, body);
        }
      }
    }

    static Bpl.Expr BplForall(Bpl.Variable arg, Bpl.Trigger trg, Bpl.Expr body) {
      return BplForall(Singleton(arg), trg, body);
    }

    static Bpl.Expr BplForall(Bpl.IToken tok, List<Bpl.TypeVariable> typeParams,
      List<Bpl.Variable> formals, Bpl.QKeyValue kv, Bpl.Trigger triggers, Bpl.Expr body, bool immutable = false) {
      return (typeParams.Count == 0 && formals.Count == 0) ? body
        : new Bpl.ForallExpr(tok, typeParams, formals, kv, triggers, body, immutable);
    }

    static Bpl.Expr BplAnd(IEnumerable<Bpl.Expr> conjuncts) {
      Contract.Requires(conjuncts != null);
      Bpl.Expr eq = Bpl.Expr.True;
      foreach (var c in conjuncts) {
        eq = BplAnd(eq, c);
      }
      return eq;
    }

    static Bpl.Expr BplAnd(Bpl.Expr a, Bpl.Expr b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      if (a == Bpl.Expr.True) {
        return b;
      } else if (b == Bpl.Expr.True) {
        return a;
      } else {
        return Bpl.Expr.Binary(a.tok, Bpl.BinaryOperator.Opcode.And, a, b);
      }
    }

    static Bpl.Expr BplOr(IEnumerable<Bpl.Expr> disjuncts) {
      Contract.Requires(disjuncts != null);
      Bpl.Expr eq = Bpl.Expr.False;
      foreach (var d in disjuncts) {
        eq = BplOr(eq, d);
      }
      return eq;
    }

    static Bpl.Expr BplOr(Bpl.Expr a, Bpl.Expr b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      if (a == Bpl.Expr.False) {
        return b;
      } else if (b == Bpl.Expr.False) {
        return a;
      } else {
        return Bpl.Expr.Binary(a.tok, Bpl.BinaryOperator.Opcode.Or, a, b);
      }
    }

    Bpl.Expr BplIff(Bpl.Expr a, Bpl.Expr b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      if (a == Bpl.Expr.True) {
        return b;
      } else if (b == Bpl.Expr.True) {
        return a;
      } else {
        return Bpl.Expr.Iff(a, b);
      }
    }

    static Bpl.Expr BplImp(Bpl.Expr a, Bpl.Expr b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      if (a == Bpl.Expr.True || b == Bpl.Expr.True) {
        return b;
      } else if (a == Bpl.Expr.False) {
        return Bpl.Expr.True;
      } else {
        return Bpl.Expr.Imp(a, b);
      }
    }

    private void BplIfIf(Bpl.IToken tk, bool yes, Bpl.Expr guard, BoogieStmtListBuilder builder, Action<BoogieStmtListBuilder> k) {
      if (yes) {
        var newBuilder = new BoogieStmtListBuilder(builder.tran, options);
        k(newBuilder);
        builder.Add(new Bpl.IfCmd(tk, guard, newBuilder.Collect(tk), null, null));
      } else {
        k(builder);
      }
    }

    /// <summary>
    /// lhs should be a Bpl.IdentifierExpr.
    /// Creates lhs := rhs;
    /// </summary>
    static Bpl.Cmd BplSimplestAssign(Bpl.Expr lhs, Bpl.Expr rhs) {
      Contract.Requires(lhs is Bpl.IdentifierExpr);
      return new Bpl.AssignCmd(rhs.tok,
        Singleton((Bpl.AssignLhs)new Bpl.SimpleAssignLhs(rhs.tok, (Bpl.IdentifierExpr)lhs)),
        Singleton(rhs));
    }

    /// Makes a simple trigger
    static Bpl.Trigger BplTrigger(Bpl.Expr e) {
      return new Bpl.Trigger(e.tok, true, new List<Bpl.Expr> { e });
    }

    static Bpl.Trigger BplTriggerHeap(Translator translator, Bpl.IToken tok, Bpl.Expr e, Bpl.Expr/*?*/ optionalHeap, Bpl.Expr/*?*/ ePrime = null) {
      Contract.Requires(translator != null);
      Contract.Requires(tok != null);
      Contract.Requires(e != null);

      var exprs = new List<Bpl.Expr> { e };
      if (ePrime != null) {
        exprs.Add(ePrime);
      }
      if (optionalHeap != null) {
        exprs.Add(translator.FunctionCall(tok, BuiltinFunction.IsGoodHeap, null, optionalHeap));
      }
      return new Bpl.Trigger(tok, true, exprs);
    }

    static Bpl.Axiom BplAxiom(Bpl.Expr e) {
      return new Bpl.Axiom(e.tok, e);
    }

    static Bpl.Expr BplLocalVar(string name, Bpl.Type ty, List<Bpl.Variable> lvars) {
      lvars.Add(BplLocalVar(name, ty, out var v));
      return v;
    }

    static Bpl.LocalVariable BplLocalVar(string name, Bpl.Type ty, out Bpl.Expr e) {
      Contract.Requires(ty != null);
      var v = new Bpl.LocalVariable(ty.tok, new Bpl.TypedIdent(ty.tok, name, ty));
      e = new Bpl.IdentifierExpr(ty.tok, name, ty);
      return v;
    }

    /* This function allows you to replace, for example:

           Bpl.BoundVariable iVar = new Bpl.BoundVariable(e.tok, new Bpl.TypedIdent(e.tok, "$i", Bpl.Type.Int));
           Bpl.IdentifierExpr i = new Bpl.IdentifierExpr(e.tok, iVar);

       with:

           Bpl.Expr i; var iVar = BplBoundVar("$i", Bpl.Type.Int, out i);
    */
    static Bpl.BoundVariable BplBoundVar(string name, Bpl.Type ty, out Bpl.Expr e) {
      Contract.Requires(ty != null);
      var v = new Bpl.BoundVariable(ty.tok, new Bpl.TypedIdent(ty.tok, name, ty));
      e = new Bpl.IdentifierExpr(ty.tok, name, ty);
      return v;
    }

    static Bpl.Expr BplBoundVar(string name, Bpl.Type ty, List<Bpl.Variable> bvars) {
      bvars.Add(BplBoundVar(name, ty, out var e));
      return e;
    }

    // Makes a formal variable
    static Bpl.Formal BplFormalVar(string/*?*/ name, Bpl.Type ty, bool incoming) {
      return BplFormalVar(name, ty, incoming, out _);
    }

    static Bpl.Formal BplFormalVar(string/*?*/ name, Bpl.Type ty, bool incoming, out Bpl.Expr e, Bpl.Expr whereClause = null) {
      if (name == null) {
        name = Bpl.TypedIdent.NoName;
      }
      var res = new Bpl.Formal(ty.tok, new Bpl.TypedIdent(ty.tok, name, ty, whereClause), incoming);
      e = new Bpl.IdentifierExpr(ty.tok, res);
      return res;
    }

    static Bpl.Expr BplFormalVar(string name, Bpl.Type ty, bool incoming, List<Bpl.Variable> fvars) {
      fvars.Add(BplFormalVar(name, ty, incoming, out var e));
      return e;
    }

    public static IToken ToDafnyToken(Bpl.IToken exprTok) {
      if (exprTok == null) {
        return null;
      } else if (exprTok is IToken t) {
        return t;
      } else if (exprTok == Boogie.Token.NoToken) {
        return Token.NoToken;
      } else {

        Uri uri = null;
        try {
          uri = new Uri(exprTok.filename);
        } catch (UriFormatException e) {
          
        }
        // These boogie Tokens can be created by TokenTextWriter
        // This is defensive programming but we aren't expecting to hit this case
        return new Token {
          col = exprTok.col,
          Uri = uri,
          kind = exprTok.kind,
          LeadingTrivia = "",
          line = exprTok.line,
          Next = null,
          pos = exprTok.pos,
          TrailingTrivia = "",
          val = exprTok.val
        };
      }
    }
  }
}
