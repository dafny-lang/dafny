using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Dafny.Auditor;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny;

public abstract class MemberDecl : Declaration, ISymbol {
  public abstract string WhatKind { get; }
  public string WhatKindAndName => $"{WhatKind} '{Name}'";
  public virtual string WhatKindMentionGhost => (IsGhost ? "ghost " : "") + WhatKind;
  protected bool hasStaticKeyword;
  public bool HasStaticKeyword => hasStaticKeyword;
  public virtual bool IsStatic {
    get {
      return HasStaticKeyword || EnclosingClass is DefaultClassDecl;
    }
  }

  public virtual bool IsOpaque => false;

  protected bool isGhost;
  public bool IsGhost { get { return isGhost; } }

  public string ModifiersAsString() {
    string result = "";
    if (IsGhost) {
      result += "ghost ";
    }
    if (IsStatic) {
      result += "static ";
    }
    if (IsOpaque) {
      result += "opaque ";
    }
    return result;
  }

  /// <summary>
  /// The term "instance independent" can be confusing. It means that the constant does not get its value in
  /// a constructor. (But the RHS of the const's declaration may mention "this".)
  /// </summary>
  public bool IsInstanceIndependentConstant => this is ConstantField cf && cf.Rhs != null;

  public TopLevelDecl EnclosingClass;  // filled in during resolution
  [FilledInDuringResolution] public MemberDecl RefinementBase;  // filled in during the pre-resolution refinement transformation; null if the member is new here
  [FilledInDuringResolution] public MemberDecl OverriddenMember;  // non-null if the member overrides a member in a parent trait
  public virtual bool IsOverrideThatAddsBody => OverriddenMember != null;

  /// <summary>
  /// Returns "true" if "this" is a (possibly transitive) override of "possiblyOverriddenMember".
  /// </summary>
  public bool Overrides(MemberDecl possiblyOverriddenMember) {
    Contract.Requires(possiblyOverriddenMember != null);
    for (var th = this; th != null; th = th.OverriddenMember) {
      if (th == possiblyOverriddenMember) {
        return true;
      }
    }
    return false;
  }

  protected MemberDecl(Cloner cloner, MemberDecl original) : base(cloner, original) {
    this.hasStaticKeyword = original.hasStaticKeyword;
    this.EnclosingClass = original.EnclosingClass;
    this.isGhost = original.isGhost;
  }

  protected MemberDecl(IOrigin rangeOrigin, Name name, bool hasStaticKeyword, bool isGhost, Attributes attributes, bool isRefining)
    : base(rangeOrigin, name, attributes, isRefining) {
    Contract.Requires(rangeOrigin != null);
    Contract.Requires(name != null);
    this.hasStaticKeyword = hasStaticKeyword;
    this.isGhost = isGhost;
  }
  /// <summary>
  /// Returns className+"."+memberName.  Available only after resolution.
  /// </summary>
  public virtual string FullDafnyName {
    get {
      Contract.Requires(EnclosingClass != null);
      Contract.Ensures(Contract.Result<string>() != null);
      string n = EnclosingClass.FullDafnyName;
      return (n.Length == 0 ? n : (n + ".")) + Name;
    }
  }
  public virtual string FullName {
    get {
      Contract.Requires(EnclosingClass != null);
      Contract.Ensures(Contract.Result<string>() != null);

      return EnclosingClass.FullName + "." + Name;
    }
  }

  public override string SanitizedName =>
    (Name == EnclosingClass.Name ? "_" : "") + base.SanitizedName;

  public override string GetCompileName(DafnyOptions options) =>
    (Name == EnclosingClass.Name ? "_" : "") + base.GetCompileName(options);

  public virtual string FullSanitizedName {
    get {
      Contract.Requires(EnclosingClass != null);
      Contract.Ensures(Contract.Result<string>() != null);

      if (Name == "requires") {
        return BoogieGenerator.Requires(((ArrowTypeDecl)EnclosingClass).Arity);
      } else if (Name == "reads") {
        return BoogieGenerator.Reads(((ArrowTypeDecl)EnclosingClass).Arity);
      } else {
        return EnclosingClass.FullSanitizedName + "." + SanitizedName;
      }
    }
  }

  public virtual IEnumerable<Expression> SubExpressions => Enumerable.Empty<Expression>();

  public override IEnumerable<Assumption> Assumptions(Declaration decl) {
    foreach (var a in base.Assumptions(this)) {
      yield return a;
    }
    if (this.HasUserAttribute("only", out _)) {
      yield return new Assumption(decl, Tok, AssumptionDescription.MemberOnly);
    }
  }

  public void RecursiveCallParameters(IOrigin tok, List<TypeParameter> typeParams, List<Formal> ins,
    Expression receiverSubst, Dictionary<IVariable, Expression> substMap,
    out Expression receiver, out List<Expression> arguments) {
    Contract.Requires(tok != null);
    Contract.Requires(this != null);
    Contract.Requires(EnclosingClass is TopLevelDeclWithMembers);
    Contract.Requires(typeParams != null);
    Contract.Requires(ins != null);
    // receiverSubst is allowed to be null
    Contract.Requires(substMap != null);
    Contract.Ensures(Contract.ValueAtReturn(out receiver) != null);
    Contract.Ensures(Contract.ValueAtReturn(out arguments) != null);

    if (IsStatic) {
      receiver = new StaticReceiverExpr(tok, (TopLevelDeclWithMembers)EnclosingClass, true); // this also resolves it
    } else if (receiverSubst != null) {
      receiver = receiverSubst;
    } else {
      receiver = new ImplicitThisExpr(tok);
      receiver.Type = ModuleResolver.GetReceiverType(tok, this);  // resolve here
    }

    arguments = new List<Expression>();
    foreach (var inFormal in ins) {
      Expression inE;
      if (substMap.TryGetValue(inFormal, out inE)) {
        arguments.Add(inE);
      } else {
        var ie = new IdentifierExpr(inFormal.Tok, inFormal.Name);
        ie.Var = inFormal;  // resolve here
        ie.Type = inFormal.Type;  // resolve here
        arguments.Add(ie);
      }
    }
  }
}