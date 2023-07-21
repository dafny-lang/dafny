using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public abstract class TopLevelDecl : Declaration, TypeParameter.ParentType {
  public abstract string WhatKind { get; }
  public ModuleDefinition EnclosingModuleDefinition;
  public readonly List<TypeParameter> TypeArgs;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(cce.NonNullElements(TypeArgs));
  }

  protected TopLevelDecl(Cloner cloner, TopLevelDecl original, ModuleDefinition parent) : base(cloner, original) {
    TypeArgs = original.TypeArgs.ConvertAll(cloner.CloneTypeParam);
    EnclosingModuleDefinition = parent;
  }

  protected TopLevelDecl(RangeToken rangeToken, Name name, ModuleDefinition enclosingModule, List<TypeParameter> typeArgs, Attributes attributes, bool isRefining)
    : base(rangeToken, name, attributes, isRefining) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(cce.NonNullElements(typeArgs));
    EnclosingModuleDefinition = enclosingModule;
    TypeArgs = typeArgs;
  }

  public string FullDafnyName {
    get {
      if (Name == "_module") {
        return "";
      }

      if (Name == "_default") {
        return EnclosingModuleDefinition.FullDafnyName;
      }

      string n = EnclosingModuleDefinition.FullDafnyName;
      return (n.Length == 0 ? n : (n + ".")) + Name;
    }
  }
  public virtual string FullName {
    get {
      if (EnclosingModuleDefinition is null) {
        return Name;
      }
      return EnclosingModuleDefinition.FullName + "." + Name;
    }
  }
  public string FullSanitizedName {
    get {
      if (EnclosingModuleDefinition is null) {
        return SanitizedName;
      }
      return EnclosingModuleDefinition.SanitizedName + "." + SanitizedName;
    }
  }

  public string FullNameInContext(ModuleDefinition context) {
    if (EnclosingModuleDefinition == context) {
      return Name;
    } else {
      return EnclosingModuleDefinition.Name + "." + Name;
    }
  }

  public string GetFullCompileName(DafnyOptions options) {
    var externArgs = Attributes.FindExpressions(this.Attributes, "extern");
    if (!options.DisallowExterns && externArgs != null) {
      if (externArgs.Count == 2 && externArgs[0] is StringLiteralExpr && externArgs[1] is StringLiteralExpr) {
        return externArgs[0].AsStringLiteral() + "." + externArgs[1].AsStringLiteral();
      }
    }

    return options.Backend.GetCompileName(EnclosingModuleDefinition.IsDefaultModule,
      EnclosingModuleDefinition.GetCompileName(options), GetCompileName(options));
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
  /// </summary>
  public virtual List<Type> ParentTypes(List<Type> typeArgs) {
    Contract.Requires(typeArgs != null);
    Contract.Requires(this.TypeArgs.Count == typeArgs.Count);
    return new List<Type>();
  }

  public bool AllowsAllocation => true;
  public override IEnumerable<Node> Children => Enumerable.Empty<Node>();

  /// <summary>
  /// A top-level declaration is considered "essentially empty" if there is no way it could generate any resolution error
  /// other than introducing a duplicate name.
  /// </summary>
  public virtual bool IsEssentiallyEmpty() {
    return Attributes == null || TypeArgs.Count != 0;
  }
}