//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class TypeRefinementWrapper : TypeProxy {
  private static int count = 0;
  public readonly int UniqueId = count++;
  public TypeRefinementWrapper(Type t) : base() {
    T = t;
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
  /// Normalize, but don't skip over any TypeRefinementWrapper
  /// </summary>
  public static Type NormalizeSansRefinementWrappers(Type ty) {
    while (ty is not TypeRefinementWrapper) {
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
    var normalizedType = TypeRefinementWrapper.NormalizeSansRefinementWrappers(unnormalizedType);
    return (normalizedType as TypeRefinementWrapper)?.T ?? normalizedType;
  }

  public static string ToStringShowingWrapper(Type type) {
    type = NormalizeSansRefinementWrappers(type);
    if (type is TypeRefinementWrapper utp) {
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
        return $"({arrowType.Args.Comma(ToStringShowingWrapper)}) {arrow} {ToStringShowingWrapper(arrowType.Result)}";
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
    return $"{headName}<{type.TypeArgs.Comma(ToStringShowingWrapper)}>";
  }

  public static string ToStringAsBottom(Type type) {
    if (type is BottomTypePlaceholder) {
      return "\\bot";
    }
    type = NormalizeSansRefinementWrappers(type);
    if (type is TypeRefinementWrapper { IsBottomType: true }) {
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
      type = NormalizeSansRefinementWrappers(type);
      if (type is TypeRefinementWrapper updatableTypeProxy) {
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
  public BottomTypePlaceholder(Type t) {
    T = t;
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
