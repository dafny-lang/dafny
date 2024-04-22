//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

namespace Microsoft.Dafny.Compilers;

public static class CompilerTypeExtensions {
  /// <summary>
  /// Trim away newtypes to get to an ancestor type that either is not a newtype or is a native type.
  /// The method differs from Type.NormalizeToAncestorType() in that GetRuntimeType() stops at native types.
  /// </summary>
  public static Type GetRuntimeType(this Type typ) {
    while (typ.AsNewtype is { NativeType: null } newtypeDecl) {
      typ = newtypeDecl.ConcreteBaseType(typ.TypeArgs);
    }
    return typ.NormalizeExpand();
  }

}
