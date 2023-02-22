using System.Collections.Generic;

namespace Microsoft.Dafny;

public abstract class MethodOrFunction : MemberDecl {
  public readonly List<TypeParameter> TypeArgs;
  public readonly List<AttributedExpression> Req;
  public readonly List<AttributedExpression> Ens;
  public readonly Specification<Expression> Decreases;

  protected MethodOrFunction(RangeToken rangeToken, Name name, bool hasStaticKeyword, bool isGhost,
    Attributes attributes, bool isRefining, List<TypeParameter> typeArgs,
    List<AttributedExpression> req,
    List<AttributedExpression> ens,
    Specification<Expression> decreases)
    : base(rangeToken, name, hasStaticKeyword, isGhost, attributes, isRefining) {
    TypeArgs = typeArgs;
    Req = req;
    Decreases = decreases;
    Ens = ens;
  }

  protected abstract bool Bodyless { get; }
  protected abstract string TypeName { get; }

  public bool IsVirtual => EnclosingClass is TraitDecl && !IsStatic;

  public virtual void Resolve(Resolver resolver) {
    if (Bodyless && !IsVirtual && !this.IsExtern() && !this.IsExplicitAxiom()) {
      foreach (var ensures in Ens) {
        if (!ensures.IsExplicitAxiom() && !resolver.Options.Get(CommonOptionBag.AllowAxioms)) {
          resolver.Reporter.Warning(MessageSource.Resolver, ErrorDetail.ErrorID.None, ensures.Tok,
            $"This ensures clause is part of a bodyless {TypeName}. Add the {{:axiom}} attribute to it or the enclosing {TypeName} to suppress this warning");
        }
      }
    }
  }

  protected MethodOrFunction(RangeToken tok, Name name, bool hasStaticKeyword, bool isGhost, Attributes attributes, bool isRefining) : base(tok, name, hasStaticKeyword, isGhost, attributes, isRefining) {
  }
}