using System.Collections.Generic;
using Microsoft.Dafny.Auditor;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class TraitDecl : ClassLikeDecl {
  public override string WhatKind => "trait";
  public bool IsParent { set; get; }
  public override bool AcceptThis => true;

  internal void SetUpAsReferenceType(bool isReferenceType) {
    // Note, it's important to set .NonNullTypeDecl first, before calling NewSelfSynonym(), since the latter will look at the former.
    Contract.Assert(NonNullTypeDecl == null); // SetUpAsReferenceType should be called only once
    if (isReferenceType) {
      NonNullTypeDecl = new NonNullTypeDecl(this);
    }

    this.NewSelfSynonym();
  }

  public override bool IsReferenceTypeDecl => NonNullTypeDecl != null;

  /// <summary>
  /// This constructor creates a TraitDecl object. However, before the object really functions as a TraitDecl, it is necessary
  /// to call SetUpAsReferenceType, which sets .NonNullTypeDecl (if necessary) and calls NewSelfSynonym().
  /// </summary>
  public TraitDecl(IOrigin origin, Name nameNode, ModuleDefinition enclosingModule,
    List<TypeParameter> typeArgs, [Captured] List<MemberDecl> members, Attributes attributes, bool isRefining, List<Type> /*?*/ traits)
    : base(origin, nameNode, attributes, typeArgs, enclosingModule, members, traits) {
    IsRefining = isRefining;
  }

  public override bool IsRefining { get; }

  public override IEnumerable<Assumption> Assumptions(Declaration decl) {
    foreach (var assumption in base.Assumptions(this)) {
      yield return assumption;
    }

    if (Attributes.Find(Attributes, "termination") is { } ta &&
        ta.Args.Count == 1 && Expression.IsBoolLiteral(ta.Args[0], out var termCheck) &&
        termCheck == false) {
      yield return new Assumption(this, Origin, AssumptionDescription.HasTerminationFalseAttribute);
    }
  }
}