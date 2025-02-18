using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Dafny.Auditor;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny;

public abstract class Declaration : RangeNode, IAttributeBearingDeclaration, ISymbol {
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Name != null);
  }

  public IOrigin BodyStartTok = Token.NoToken;
  public Name NameNode;

  public virtual IOrigin NavigationToken => NameNode.Origin;

  public string Name => NameNode.Value;
  public virtual bool IsRefining => false;

  private VisibilityScope opaqueScope = new();
  private VisibilityScope revealScope = new();

  private bool scopeIsInherited = false;

  protected Declaration(Cloner cloner, Declaration original) : base(cloner, original) {
    NameNode = original.NameNode.Clone(cloner);
    BodyStartTok = cloner.Origin(original.BodyStartTok);
    Attributes = cloner.CloneAttributes(original.Attributes);
  }

  protected Declaration(IOrigin origin, Name name, Attributes attributes) : base(origin) {
    Contract.Requires(origin != null);
    Contract.Requires(name != null);
    this.NameNode = name;
    this.Attributes = attributes;
  }

  public bool HasAxiomAttribute =>
    Attributes.Contains(Attributes, Attributes.AxiomAttributeName);

  public bool HasConcurrentAttribute =>
    Attributes.Contains(Attributes, Attributes.ConcurrentAttributeName);

  public bool HasExternAttribute =>
    Attributes.Contains(Attributes, Attributes.ExternAttributeName);

  public bool HasAutoGeneratedAttribute =>
    Attributes.Contains(Attributes, Attributes.AutoGeneratedAttributeName);

  public bool HasVerifyFalseAttribute =>
    Attributes.Find(Attributes, Attributes.VerifyAttributeName) is { } va &&
    va.Args.Count == 1 &&
    Expression.IsBoolLiteral(va.Args[0], out var verify) &&
    verify == false;

  public override IEnumerable<Assumption> Assumptions(Declaration decl) {
    if (HasAxiomAttribute && !HasAutoGeneratedAttribute) {
      yield return new Assumption(this, Origin, AssumptionDescription.HasAxiomAttribute);
    }

    if (HasVerifyFalseAttribute && !HasAutoGeneratedAttribute) {
      yield return new Assumption(this, Origin, AssumptionDescription.HasVerifyFalseAttribute);
    }
  }

  public virtual bool CanBeExported() {
    return true;
  }

  public virtual bool CanBeRevealed() {
    return false;
  }

  public bool ScopeIsInherited { get { return scopeIsInherited; } }

  public void AddVisibilityScope(VisibilityScope scope, bool isOpaque) {
    if (isOpaque) {
      opaqueScope.Augment(scope);
    } else {
      revealScope.Augment(scope);
    }
  }

  public void InheritVisibility(Declaration d, bool onlyRevealed = true) {
    Contract.Assert(opaqueScope.IsEmpty());
    Contract.Assert(revealScope.IsEmpty());
    scopeIsInherited = false;

    revealScope = d.revealScope;

    if (!onlyRevealed) {
      opaqueScope = d.opaqueScope;
    }
    scopeIsInherited = true;

  }

  public bool IsRevealedInScope(VisibilityScope scope) {
    return revealScope.VisibleInScope(scope);
  }

  public bool IsVisibleInScope(VisibilityScope scope) {
    return IsRevealedInScope(scope) || opaqueScope.VisibleInScope(scope);
  }

  protected string sanitizedName;
  public virtual string SanitizedName => sanitizedName ??= NonglobalVariable.SanitizeName(Name);

  protected string compileName;

  public virtual string GetCompileName(DafnyOptions options) {
    if (compileName == null) {
      this.IsExtern(options, out _, out compileName);
      compileName ??= SanitizedName;
    }

    return compileName;
  }

  public Attributes Attributes;  // readonly, except during class merging in the refinement transformations and when changed by Compiler.MarkCapitalizationConflict
  Attributes IAttributeBearingDeclaration.Attributes {
    get => Attributes;
    set => Attributes = value;
  }
  string IAttributeBearingDeclaration.WhatKind =>
    this is TopLevelDecl topLevelDecl
      ? topLevelDecl.WhatKind
      : this is MemberDecl memberDecl
      ? memberDecl.WhatKind
      : "declaration";

  [Pure]
  public override string ToString() {
    Contract.Ensures(Contract.Result<string>() != null);
    return Name;
  }

  // For Boogie
  internal VerificationIdGenerator IdGenerator = new();
  public override IEnumerable<INode> Children => []; // Attributes should be enumerated by the parent, as they could be placed in different places
  public override IEnumerable<INode> PreResolveChildren => Children;
  public abstract SymbolKind? Kind { get; }
  public abstract string GetDescription(DafnyOptions options);


  // For Compilation
  internal CodeGenIdGenerator CodeGenIdGenerator = new();
}