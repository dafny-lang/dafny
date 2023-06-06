using System.Collections.Generic;
using Microsoft.Dafny.Auditor;

namespace Microsoft.Dafny;

public class TraitDecl : ClassLikeDecl {
  public override string WhatKind => "trait";
  public bool IsParent { set; get; }
  public override bool AcceptThis => true;

  public override bool IsReferenceTypeDecl => true; // SOON: IsObjectTrait || ParentTraits.Any(parent => parent.IsRefType);

  public TraitDecl(RangeToken rangeToken, Name name, ModuleDefinition module,
    List<TypeParameter> typeArgs, [Captured] List<MemberDecl> members, Attributes attributes, bool isRefining, List<Type> /*?*/ traits)
    : base(rangeToken, name, module, typeArgs, members, attributes, isRefining, traits) {

    NonNullTypeDecl = new NonNullTypeDecl(this); // SOON: this should be done only if the trait is a reference type
    this.NewSelfSynonym();
  }

  public override IEnumerable<Assumption> Assumptions(Declaration decl) {
    foreach (var assumption in base.Assumptions(this)) {
      yield return assumption;
    }

    if (Attributes.Find(Attributes, "termination") is { } ta &&
        ta.Args.Count == 1 && Expression.IsBoolLiteral(ta.Args[0], out var termCheck) &&
        termCheck == false) {
      yield return new Assumption(this, tok, AssumptionDescription.HasTerminationFalseAttribute);
    }
  }
}