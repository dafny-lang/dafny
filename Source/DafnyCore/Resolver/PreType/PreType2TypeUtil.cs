//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System.Diagnostics.Contracts;
using System.Collections.Generic;
using JetBrains.Annotations;

namespace Microsoft.Dafny;

public static class PreType2TypeUtil {
  public static Type PreType2Type(PreType preType, bool allowFutureAdjustments, TypeParameter.TPVariance futureAdjustments) {
    if (allowFutureAdjustments) {
      return PreType2AdjustableType(preType, futureAdjustments);
    } else {
      return PreType2FixedType(preType);
    }
  }

  public static Type PreType2FixedType(PreType preType) {
    return PreType2TypeCore(preType, false, TypeParameter.TPVariance.Co);
  }

  public static Type PreType2AdjustableType(PreType preType, TypeParameter.TPVariance futureAdjustments) {
    var ty = PreType2TypeCore(preType, true, futureAdjustments);
    switch (futureAdjustments) {
      case TypeParameter.TPVariance.Co:
        ty = new BottomTypePlaceholder(ty);
        break;
      default:
        break;
    }

    return new AdjustableType(ty);
  }

  /// <summary>
  /// The "futureAdjustment" parameter is relevant only if "allowFutureAdjustments" is "true".
  /// </summary>
  private static Type PreType2TypeCore(PreType preType, bool allowFutureAdjustments, TypeParameter.TPVariance futureAdjustments) {
    var pt = (DPreType)preType.Normalize(); // all pre-types should have been filled in and resolved to a non-proxy
    if (pt.PrintablePreType != null) {
      pt = pt.PrintablePreType;
    }

    Type ArgumentAsCo(int i) {
      return PreType2Type(pt.Arguments[i], true, futureAdjustments);
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
        return new SetType(true, ArgumentAsCo(0));
      case "iset":
        return new SetType(false, ArgumentAsCo(0));
      case "multiset":
        return new MultiSetType(ArgumentAsCo(0));
      case "seq":
        return new SeqType(ArgumentAsCo(0));
      case "map":
        return new MapType(true, ArgumentAsCo(0), ArgumentAsCo(1));
      case "imap":
        return new MapType(false, ArgumentAsCo(0), ArgumentAsCo(1));
      default:
        break;
    }

    var arguments = pt.Arguments.ConvertAll(preType => PreType2AdjustableType(preType, futureAdjustments));
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

  public static void Combine(Type userSuppliedType, PreType preType, bool allowFutureAdjustments) {
    var preTypeConverted = PreType2Type(preType, allowFutureAdjustments, TypeParameter.TPVariance.Co);
    Combine(userSuppliedType, preTypeConverted);
  }

  /// <summary>
  /// This method combines the respective user-supplied types with the inferred pre-types. It expects that either
  ///     - "types" is null, which represents the case where the types are inferred. In this case, the method returns a new
  ///       list that contains the converted pre-types.
  ///     - "types" is non-null, which represents the case where the user supplied types. In this case, "types" and
  ///       "preTypes" are expected to have the same length. The respective types and pre-types are combined in "types",
  ///       and then "types" is returned.
  /// </summary>
  public static List<Type> Combine([CanBeNull] List<Type> types, List<PreType> preTypes, bool allowFutureAdjustments) {
    Contract.Requires(types == null || types.Count == preTypes.Count);
    if (types == null) {
      if (allowFutureAdjustments) {
        return preTypes.ConvertAll(preType => PreType2AdjustableType(preType, TypeParameter.TPVariance.Co));
      } else {
        return preTypes.ConvertAll(PreType2FixedType);
      }
    }

    Contract.Assert(types.Count == preTypes.Count);
    for (var i = 0; i < types.Count; i++) {
      Combine(types[i], preTypes[i], allowFutureAdjustments);
    }
    return types;
  }

  private static void Combine(Type type, Type preTypeConverted) {
    Contract.Requires(type != null);
    Contract.Requires(preTypeConverted != null);

    type = type.NormalizeAndAdjustForScope();
    if (type is TypeProxy { T: null } typeProxy) {
      typeProxy.T = preTypeConverted;
    } else {
      // Even if the head type of preTypeConverted is adjustable, we're going to stick with the user-defined type, so we Normalize() here.
      preTypeConverted = preTypeConverted.Normalize();

      Contract.Assert((type as UserDefinedType)?.ResolvedClass == (preTypeConverted as UserDefinedType)?.ResolvedClass);
      Contract.Assert(type.TypeArgs.Count == preTypeConverted.TypeArgs.Count);
      for (var i = 0; i < type.TypeArgs.Count; i++) {
        // TODO: the following should take variance into consideration
        Combine(type.TypeArgs[i], preTypeConverted.TypeArgs[i]);
      }
    }
  }

}