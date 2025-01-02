using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

/// <summary>
/// The "ValuetypeDecl" class models the built-in value types (like bool, int, set, and seq.
/// Its primary function is to hold the formal type parameters and built-in members of these types.
/// </summary>
public class ValuetypeDecl : TopLevelDeclWithMembers {
  public override string WhatKind { get { return "type"; } }
  readonly Func<Type, bool> typeTester;
  readonly Func<List<Type>, Type>/*?*/ typeCreator;

  public override bool AcceptThis => true;

  public ValuetypeDecl(string name, ModuleDefinition module, Func<Type, bool> typeTester, Func<List<Type>, Type> typeCreator /*?*/)
    : base(SourceOrigin.NoToken, new Name(name), module, new List<TypeParameter>(), new List<MemberDecl>(), null, false, null) {
    Contract.Requires(name != null);
    Contract.Requires(module != null);
    Contract.Requires(typeTester != null);
    this.typeTester = typeTester;
    this.typeCreator = typeCreator;
  }

  public ValuetypeDecl(string name, ModuleDefinition module, List<TypeParameter.TPVarianceSyntax> typeParameterVariance,
    Func<Type, bool> typeTester, Func<List<Type>, Type>/*?*/ typeCreator)
    : this(name, module, typeTester, typeCreator) {
    Contract.Requires(name != null);
    Contract.Requires(module != null);
    Contract.Requires(typeTester != null);
    // fill in the type parameters
    if (typeParameterVariance != null) {
      for (int i = 0; i < typeParameterVariance.Count; i++) {
        var variance = typeParameterVariance[i];
        var tp = new TypeParameter(SourceOrigin.NoToken, new Name(((char)('T' + i)).ToString()), variance) {
          Parent = this,
          PositionalIndex = i
        };
        TypeArgs.Add(tp);
      }
    }
  }

  public ValuetypeDecl(string name, ModuleDefinition module, List<TypeParameter> typeParameters,
    List<MemberDecl> members, Attributes attributes, Func<Type, bool> typeTester, Func<List<Type>, Type> /*?*/ typeCreator)
    : base(SourceOrigin.NoToken, new Name(name), module, typeParameters, members, attributes, false) {
    this.typeTester = typeTester;
    this.typeCreator = typeCreator;
  }

  public bool IsThisType(Type t) {
    Contract.Assert(t != null);
    return typeTester(t);
  }

  public Type CreateType(List<Type> typeArgs) {
    Contract.Requires(typeArgs != null);
    Contract.Requires(typeArgs.Count == TypeArgs.Count);
    Contract.Assume(typeCreator != null);  // can only call CreateType for a ValuetypeDecl with a type creator (this is up to the caller to ensure)
    return typeCreator(typeArgs);
  }
}