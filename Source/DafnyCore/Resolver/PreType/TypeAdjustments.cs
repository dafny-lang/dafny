//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class AdjustableType : TypeProxy {
  private static int count = 0;
  public readonly int UniqueId = count++;
  public AdjustableType(Type type) : base() {
    T = new BottomTypePlaceholder(type);
  }

  public bool IsBottomType => T is BottomTypePlaceholder;

  public override string TypeName(DafnyOptions options, ModuleDefinition context, bool parseAble) {
    var baseName = base.TypeName(options, context, parseAble);
    if (options.Get(CommonOptionBag.NewTypeInferenceDebug)) {
      return $"/*%{UniqueId}*/{baseName}";
    } else {
      return baseName;
    }
  }

  /// <summary>
  /// Normalize, but don't skip over any AdjustableType
  /// </summary>
  public static Type NormalizeSansAdjustableType(Type ty) {
    while (ty is not AdjustableType) {
      if (ty is TypeProxy { T: { } proxyFor }) {
        ty = proxyFor;
      } else {
        break;
      }
    }
    return ty;
  }

  public static string ToStringAsAdjustableType(Type type) {
    type = NormalizeSansAdjustableType(type);
    if (type is AdjustableType utp) {
      return $"%{utp.UniqueId}";
    } else {
      return type.ToString();
    }
  }

  public static string ToStringAsBottom(Type type) {
    type = NormalizeSansAdjustableType(type);
    if (type is AdjustableType { IsBottomType: true}) {
      return "\\bot";
    } else {
      return type.ToString();
    }
  }

  public static bool NormalizesToBottom(Type type) {
    while (true) {
      type = NormalizeSansAdjustableType(type);
      if (type is AdjustableType updatableTypeProxy) {
        if (updatableTypeProxy.IsBottomType) {
          return true;
        }
        type = updatableTypeProxy.T;
      } else {
        return false;
      }
    }
  }
}

public class TypeAdjustments {
  public static Type PreType2Type(PreType preType) {
    return PreType2TypeCore(preType, true, false);
  }

  public static Type PreType2Type(PreType preType, bool allowFutureAdjustments) {
    if (allowFutureAdjustments) {
      return PreType2AdjustableType(preType);
    } else {
      return PreType2TypeCore(preType, true, false);
    }
  }

  public static AdjustableType PreType2AdjustableType(PreType preType) {
    var ty = PreType2TypeCore(preType, true, true);
    var proxy = new AdjustableType(ty);
    return proxy;
  }

  private static Type PreType2TypeCore(PreType preType, bool usePrintablePreType, bool allowFutureAdjustments) {
    var pt = (DPreType)preType.Normalize(); // all pre-types should have been filled in and resolved to a non-proxy
    if (usePrintablePreType && pt.PrintablePreType != null) {
      pt = pt.PrintablePreType;
    }
    switch (pt.Decl.Name) {
      case "bool":
        return Type.Bool;
      case "char":
        return Type.Char;
      case "int":
        return Type.Int;
      case "real":
        return Type.Real;
      case "ORDINAL":
        return Type.BigOrdinal;
      case "set":
        return new SetType(true, PreType2Type(pt.Arguments[0], allowFutureAdjustments));
      case "iset":
        return new SetType(false, PreType2Type(pt.Arguments[0], allowFutureAdjustments));
      case "multiset":
        return new MultiSetType(PreType2Type(pt.Arguments[0], allowFutureAdjustments));
      case "seq":
        return new SeqType(PreType2Type(pt.Arguments[0], allowFutureAdjustments));
      case "map":
        return new MapType(true, PreType2Type(pt.Arguments[0], allowFutureAdjustments), PreType2Type(pt.Arguments[1], allowFutureAdjustments));
      case "imap":
        return new MapType(false, PreType2Type(pt.Arguments[0], allowFutureAdjustments), PreType2Type(pt.Arguments[1], allowFutureAdjustments));
      default:
        break;
    }
    var arguments = pt.Arguments.ConvertAll(preType => PreType2Type(preType, allowFutureAdjustments));
    if (pt.Decl is ArrowTypeDecl arrowTypeDecl) {
      return new ArrowType(pt.Decl.tok, arrowTypeDecl, arguments);
    } else if (pt.Decl is ValuetypeDecl valuetypeDecl) {
      return valuetypeDecl.CreateType(arguments);
    } else if (pt.Decl is ClassLikeDecl { IsReferenceTypeDecl: true }) {
      return new UserDefinedType(pt.Decl.tok, pt.Decl.Name + "?", pt.Decl, arguments);
    } else {
      return new UserDefinedType(pt.Decl.tok, pt.Decl.Name, pt.Decl, arguments);
    }
  }

  private static void Combine(Type userSuppliedType, PreType preType, bool allowFutureAdjustments) {
    var preTypeConverted = PreType2TypeCore(preType, true, allowFutureAdjustments);
    Combine(userSuppliedType, preTypeConverted);
  }

  private static void Combine(Type type, Type preTypeConverted) {
    Contract.Requires(type != null);
    Contract.Requires(preTypeConverted != null);

    type = type.NormalizeExpand();
    preTypeConverted = preTypeConverted.NormalizeExpand();
    if (type is TypeProxy { T: null } typeProxy) {
      typeProxy.T = preTypeConverted;
    } else {
      Contract.Assert((type as UserDefinedType)?.ResolvedClass == (preTypeConverted as UserDefinedType)?.ResolvedClass);
      Contract.Assert(type.TypeArgs.Count == preTypeConverted.TypeArgs.Count);
      for (var i = 0; i < type.TypeArgs.Count; i++) {
        Combine(type.TypeArgs[i], preTypeConverted.TypeArgs[i]);
      }
    }
  }

}