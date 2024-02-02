//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class AdjustableType : TypeProxy {
  private static int count = 0;
  public readonly int UniqueId = count++;
  public AdjustableType(Type type) : base() {
    T = type;
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

  public static Type NormalizeSansBottom(Expression expr) {
    return NormalizeSansBottom(expr.UnnormalizedType);
  }

  public static Type NormalizeSansBottom(IVariable variable) {
    return NormalizeSansBottom(variable.UnnormalizedType);
  }

  public static Type NormalizeSansBottom(Type unnormalizedType) {
    var normalizedType = AdjustableType.NormalizeSansAdjustableType(unnormalizedType);
    return (normalizedType as AdjustableType)?.T ?? normalizedType;
  }

  public static string ToStringAsAdjustableType(Type type) {
    type = NormalizeSansAdjustableType(type);
    if (type is AdjustableType utp) {
      return $"%{utp.UniqueId}";
    }
    if (type is BasicType) {
      return type.ToString();
    }
    if (type.AsArrowType is { } arrowType) {
      string arrow = type is ArrowType
        ? "~>"
        : type is UserDefinedType userDefinedType
          ? ArrowType.IsPartialArrowTypeName(userDefinedType.Name)
            ? "-->"
            : ArrowType.IsTotalArrowTypeName(userDefinedType.Name)
              ? "->"
              : null
          : null;
      if (arrow != null) {
        return $"({arrowType.Args.Comma(ToStringAsAdjustableType)}) {arrow} {ToStringAsAdjustableType(arrowType.Result)}";
      }
    }
    string headName;
    if (type is CollectionType collectionType) {
      headName = collectionType.CollectionTypeName;
    } else if (type is UserDefinedType udt) {
      headName = udt.Name;
    } else {
      Contract.Assert(type.TypeArgs.Count == 0);
      headName = type.ToString();
    }
    if (type.TypeArgs.Count == 0) {
      return headName;
    }
    return $"{headName}<{type.TypeArgs.Comma(ToStringAsAdjustableType)}>";
  }

  public static string ToStringAsBottom(Type type) {
    if (type is BottomTypePlaceholder) {
      return "\\bot";
    }
    type = NormalizeSansAdjustableType(type);
    if (type is AdjustableType { IsBottomType: true }) {
      return "\\bot";
    } else {
      return type.ToString();
    }
  }

  public static bool NormalizesToBottom(Type type) {
    if (type is BottomTypePlaceholder) {
      return true;
    }
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

public class BottomTypePlaceholder : TypeProxy {
  public BottomTypePlaceholder(Type baseType) {
    T = baseType;
  }

  public override string TypeName(DafnyOptions options, ModuleDefinition context, bool parseAble) {
    var baseName = base.TypeName(options, context, parseAble);
    if (options.Get(CommonOptionBag.NewTypeInferenceDebug)) {
      return $"/*\\bot*/{baseName}";
    } else {
      return baseName;
    }
  }
}
