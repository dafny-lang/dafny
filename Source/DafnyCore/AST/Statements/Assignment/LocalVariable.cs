using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny;

public class LocalVariable : RangeNode, IVariable, IAttributeBearingDeclaration {
  readonly string name;
  public string DafnyName => Name;
  public Attributes Attributes;
  Attributes IAttributeBearingDeclaration.Attributes {
    get => Attributes;
    set => Attributes = value;
  }
  string IAttributeBearingDeclaration.WhatKind => "local variable";

  public bool IsGhost;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(name != null);
    Contract.Invariant(SyntacticType != null);
  }

  public override IOrigin Tok => Origin;

  public LocalVariable(Cloner cloner, LocalVariable original)
    : base(cloner, original) {
    name = original.Name;
    SyntacticType = cloner.CloneType(original.SyntacticType);
    IsTypeExplicit = original.IsTypeExplicit;
    IsGhost = original.IsGhost;

    if (cloner.CloneResolvedFields) {
      type = original.type;
    }
  }

  public LocalVariable(IOrigin rangeOrigin, string name, Type type, bool isGhost)
    : base(rangeOrigin) {
    Contract.Requires(name != null);
    Contract.Requires(type != null);  // can be a proxy, though

    this.name = name;
    IsTypeExplicit = type != null;
    this.SyntacticType = type ?? new InferredTypeProxy();
    if (type is InferredTypeProxy) {
      ((InferredTypeProxy)type).KeepConstraints = true;
    }
    this.IsGhost = isGhost;
  }

  public string Name {
    get {
      Contract.Ensures(Contract.Result<string>() != null);
      return name;
    }
  }
  public static bool HasWildcardName(IVariable v) {
    Contract.Requires(v != null);
    return v.Name.StartsWith("_v");
  }
  public static string DisplayNameHelper(IVariable v) {
    Contract.Requires(v != null);
    return HasWildcardName(v) ? $"_ /* {v.Name} */" : v.Name;
  }
  public string DisplayName {
    get { return DisplayNameHelper(this); }
  }
  private string uniqueName;
  public string UniqueName => uniqueName;
  public bool HasBeenAssignedUniqueName => uniqueName != null;
  public string AssignUniqueName(VerificationIdGenerator generator) {
    return uniqueName ??= generator.FreshId(Name + "#");
  }

  private string sanitizedNameShadowable;

  public string CompileNameShadowable =>
    sanitizedNameShadowable ??= NonglobalVariable.SanitizeName(Name);

  string compileName;

  public string GetOrCreateCompileName(CodeGenIdGenerator generator) {
    return compileName ??= $"_{generator.FreshNumericId()}_{CompileNameShadowable}";
  }

  // TODO rename and update comment? Or make it nullable?
  public readonly Type SyntacticType;  // this is the type mentioned in the declaration, if any
  Type IVariable.OptionalType => SyntacticType;

  [FilledInDuringResolution]
  internal Type type;  // this is the declared or inferred type of the variable; it is non-null after resolution (even if resolution fails)
  public Type Type {
    get {
      Contract.Ensures(Contract.Result<Type>() != null);

      Contract.Assume(type != null);  /* we assume object has been resolved */
      return type.Normalize();
    }
  }

  /// <summary>
  /// For a description of the difference between .Type and .UnnormalizedType, see Expression.UnnormalizedType.
  /// </summary>
  public Type UnnormalizedType {
    get {
      Contract.Ensures(Contract.Result<Type>() != null);

      Contract.Assume(type != null);  /* we assume object has been resolved */
      return type;
    }
  }

  public PreType PreType { get; set; }

  public bool IsMutable {
    get {
      return true;
    }
  }
  bool IVariable.IsGhost {
    get {
      return this.IsGhost;
    }
  }
  /// <summary>
  /// This method retrospectively makes the LocalVariable a ghost.  It is to be used only during resolution.
  /// </summary>
  public void MakeGhost() {
    this.IsGhost = true;
  }

  public IOrigin NavigationToken => Origin.StartToken;
  public bool IsTypeExplicit { get; }
  public override IEnumerable<INode> Children =>
    Attributes.AsEnumerable().
      Concat<Node>(
      IsTypeExplicit ? new List<Node>() { type } : Enumerable.Empty<Node>());

  public override IEnumerable<INode> PreResolveChildren =>
    Attributes.AsEnumerable().
      Concat<Node>(
      IsTypeExplicit ? new List<Node>() { SyntacticType ?? type } : Enumerable.Empty<Node>());

  public SymbolKind? Kind => SymbolKind.Variable;
  public string GetDescription(DafnyOptions options) {
    return this.AsText();
  }
}