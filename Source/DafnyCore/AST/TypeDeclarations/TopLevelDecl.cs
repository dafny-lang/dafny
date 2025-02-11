using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Newtonsoft.Json;
using NJsonSchema.Converters;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny;

[JsonConverter(typeof(JsonInheritanceConverter<TopLevelDecl>), "discriminator")]
public abstract class TopLevelDecl : Declaration, TypeParameter.ParentType {
  public abstract string WhatKind { get; }
  public string WhatKindAndName => $"{WhatKind} '{Name}'";
  [BackEdge]
  public ModuleDefinition EnclosingModule;
  public readonly List<TypeParameter> TypeArgs;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(cce.NonNullElements(TypeArgs));
  }

  protected TopLevelDecl(Cloner cloner, TopLevelDecl original, ModuleDefinition enclosingModule) : base(cloner, original) {
    TypeArgs = original.TypeArgs.ConvertAll(cloner.CloneTypeParam);
    EnclosingModule = enclosingModule;
  }

  protected TopLevelDecl(IOrigin origin, Name nameNode, Attributes attributes,
    List<TypeParameter> typeArgs, ModuleDefinition enclosingModule)
    : base(origin, nameNode, attributes) {
    Contract.Requires(origin != null);
    Contract.Requires(nameNode != null);
    Contract.Requires(cce.NonNullElements(typeArgs));
    EnclosingModule = enclosingModule;
    TypeArgs = typeArgs;
  }

  public string FullDafnyName {
    get {
      if (Name == "_module") {
        return "";
      }

      if (Name == "_default") {
        return EnclosingModule.FullDafnyName;
      }

      string n = EnclosingModule.FullDafnyName;
      return (n.Length == 0 ? n : (n + ".")) + Name;
    }
  }
  public virtual string FullName {
    get {
      if (EnclosingModule is null) {
        return Name;
      }
      return EnclosingModule.FullName + "." + Name;
    }
  }
  public string FullSanitizedName {
    get {
      if (EnclosingModule is null) {
        return SanitizedName;
      }
      return EnclosingModule.SanitizedName + "." + SanitizedName;
    }
  }

  public string FullNameInContext(ModuleDefinition context) {
    if (EnclosingModule == context) {
      return Name;
    } else {
      return EnclosingModule.Name + "." + Name;
    }
  }

  public string GetFullCompileName(DafnyOptions options) {
    var externArgs = Attributes.FindExpressions(this.Attributes, "extern");
    if (!options.DisallowExterns && externArgs != null) {
      if (externArgs.Count == 2 && externArgs[0] is StringLiteralExpr && externArgs[1] is StringLiteralExpr) {
        return externArgs[0].AsStringLiteral() + "." + externArgs[1].AsStringLiteral();
      }
    }

    return options.Backend.GetCompileName(EnclosingModule.TryToAvoidName,
      EnclosingModule.GetCompileName(options), GetCompileName(options));
  }

  public TopLevelDecl ViewAsClass {
    get {
      if (this is NonNullTypeDecl) {
        return ((NonNullTypeDecl)this).Class;
      } else {
        return this;
      }
    }
  }

  /// <summary>
  /// Return the list of parent types of "this", where the type parameters
  /// of "this" have been instantiated by "typeArgs". For example, for a subset
  /// type, the return value is the RHS type, appropriately instantiated. As
  /// two other examples, given
  ///     class C<X> extends J<X, int>
  /// C.ParentTypes(real) = J<real, int>    // non-null types C and J
  /// C?.ParentTypes(real) = J?<real, int>  // possibly-null type C? and J?
  /// 
  /// If "includeTypeBounds" is "true", then for a type parameter, ParentTypes() returns the type bounds.
  /// </summary>
  public virtual List<Type> ParentTypes(List<Type> typeArgs, bool includeTypeBounds) {
    Contract.Requires(typeArgs != null);
    Contract.Requires(this.TypeArgs.Count == typeArgs.Count);
    return [];
  }

  public bool AllowsAllocation => true;
  public override IEnumerable<INode> Children => Enumerable.Empty<Node>();

  /// <summary>
  /// A top-level declaration is considered "essentially empty" if there is no way it could generate any resolution error
  /// other than introducing a duplicate name.
  /// </summary>
  public virtual bool IsEssentiallyEmpty() {
    return Attributes == null || TypeArgs.Count != 0;
  }
}