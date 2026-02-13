using System.Collections.Generic;
using System.Diagnostics.Contracts;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny;

public class NonNullTypeDecl : SubsetTypeDecl {
  public override string WhatKind => "non-null type";
  public ClassLikeDecl Class;

  /// <summary>
  /// The public constructor is NonNullTypeDecl(ClassDecl cl). The rest is pretty crazy: There are stages of "this"-constructor calls
  /// in order to build values that depend on previously computed parameters.
  /// </summary>
  public NonNullTypeDecl(ClassLikeDecl cl)
    : this(cl, TypeParameter.CloneTypeParameters(cl.TypeArgs)) {
    Contract.Requires(cl != null);
  }

  private NonNullTypeDecl(ClassLikeDecl cl, List<TypeParameter> tps)
    : this(cl, tps,
      new BoundVar(cl.Origin, "c", new UserDefinedType(cl.Origin, cl.Name + "?", tps.Count == 0 ? null : tps.ConvertAll(tp => (Type)new UserDefinedType(tp))))) {
    Contract.Requires(cl != null);
    Contract.Requires(tps != null);
  }

  private NonNullTypeDecl(ClassLikeDecl cl, List<TypeParameter> tps, BoundVar var)
    : base(cl.Origin, cl.NameNode, new TypeParameterCharacteristics(), tps, cl.EnclosingModuleDefinition, var,
      new BinaryExpr(cl.Origin, BinaryExpr.Opcode.Neq, new IdentifierExpr(cl.Origin, var), new LiteralExpr(cl.Origin)),
      SubsetTypeDecl.WKind.Special, null, SystemModuleManager.AxiomAttribute()) {
    Contract.Requires(cl != null);
    Contract.Requires(tps != null);
    Contract.Requires(var != null);
    Class = cl;
  }

  public override List<Type> ParentTypes(List<Type> typeArgs, bool includeTypeBounds) {
    var result = new List<Type>(base.ParentTypes(typeArgs, includeTypeBounds));

    foreach (var rhsParentType in Class.ParentTypes(typeArgs, includeTypeBounds)) {
      var rhsParentUdt = (UserDefinedType)rhsParentType; // all parent types of .Class are expected to be possibly-null class types
      Contract.Assert(rhsParentUdt.ResolvedClass is TraitDecl);
      result.Add(UserDefinedType.CreateNonNullTypeIfReferenceType(rhsParentUdt));
    }

    return result;
  }

  public override SymbolKind? Kind => Class.Kind;

  public override string GetDescription(DafnyOptions options) {
    return Class.GetDescription(options);
  }
}