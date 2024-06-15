using System.Collections.Generic;
using System.CommandLine;
using System.Linq;
using DafnyCore;
using DafnyCore.Options;

namespace Microsoft.Dafny;

public abstract class MethodOrFunction : MemberDecl {
  public static readonly Option<bool> AllowExternalContracts = new("--allow-external-contracts",
    "Allow exporting callables with preconditions, and importing callables with postconditions");

  static MethodOrFunction() {
    DooFile.RegisterLibraryCheck(AllowExternalContracts, OptionCompatibility.OptionLibraryImpliesLocalError);
  }
  
  public bool IsBlind { get; set; }
  public readonly List<TypeParameter> TypeArgs;
  public readonly List<AttributedExpression> Req;
  public readonly List<AttributedExpression> Ens;
  public readonly Specification<Expression> Decreases;
  public readonly List<Formal> Ins;

  protected MethodOrFunction(RangeToken rangeToken, Name name, bool hasStaticKeyword, bool isGhost,
    Attributes attributes, bool isRefining, List<TypeParameter> typeArgs, List<Formal> ins,
    List<AttributedExpression> req,
    List<AttributedExpression> ens,
    Specification<Expression> decreases)
    : base(rangeToken, name, hasStaticKeyword, isGhost, attributes, isRefining) {
    TypeArgs = typeArgs;
    Req = req;
    Decreases = decreases;
    Ens = ens;
    Ins = ins;
  }

  protected MethodOrFunction(Cloner cloner, MethodOrFunction original) : base(cloner, original) {
    this.TypeArgs = cloner.CloneResolvedFields ? original.TypeArgs : original.TypeArgs.ConvertAll(cloner.CloneTypeParam);
    this.Req = original.Req.ConvertAll(cloner.CloneAttributedExpr);
    this.Decreases = cloner.CloneSpecExpr(original.Decreases);
    this.Ens = original.Ens.ConvertAll(cloner.CloneAttributedExpr);
    this.Ins = original.Ins.ConvertAll(p => cloner.CloneFormal(p, false));
    IsBlind = original.IsBlind;
  }

  protected abstract bool Bodyless { get; }
  protected abstract string TypeName { get; }

  public bool IsVirtual => EnclosingClass is TraitDecl && !IsStatic;
  public bool IsAbstract => EnclosingClass.EnclosingModuleDefinition.ModuleKind != ModuleKindEnum.Concrete;

  public virtual void Resolve(ModuleResolver resolver) {
    ResolveMethodOrFunction(resolver);
  }

  public abstract bool HasPostcondition { get; }

  public void ResolveMethodOrFunction(INewOrOldResolver resolver) {
    var isImported = (Bodyless || !ProgramResolver.ShouldCompile(this)) && this.IsExtern(resolver.Options);
    if (!resolver.Options.Get(AllowExternalContracts) && HasPostcondition && isImported && !HasAxiomAttribute) {
      resolver.Reporter.Warning(MessageSource.Verifier, ResolutionErrors.ErrorId.none, Tok,
        $"when a {WhatKind} is imported, meaning it has no body and an {{:extern}} annotation, " +
        $"Dafny can not guarantee that its implementation satisfies its post-conditions (its ensures clauses and outputs that are subset types). " +
        $"To silence this warning, please add an {{:axiom}} attribute or use the option '--allow-external-contracts'.");
    }

    var isExported = !Bodyless && ProgramResolver.ShouldCompile(this) && this.IsExtern(resolver.Options);
    if (!resolver.Options.Get(AllowExternalContracts) && HasPrecondition && !HasAxiomAttribute && isExported) {
      resolver.Reporter.Warning(MessageSource.Verifier, ResolutionErrors.ErrorId.none, Tok,
        $"when a {WhatKind} is exported, meaning it has a body and an {{:extern}} annotation, " +
        $"Dafny can not guarantee that it is called with arguments that satisfy its preconditions (its requires clauses and inputs that are subset types). " +
        $"To silence this warning, please add an {{:axiom}} attribute or use the option '--allow-external-contracts'");
    }
    if (!AutoGeneratedToken.Is(RangeToken) && HasVerifyFalseAttribute) {
      resolver.Reporter.Warning(MessageSource.Verifier, ResolutionErrors.ErrorId.none, Tok,
        $"The {{:verify false}} attribute should only be used during development. " +
        $"Consider using a bodyless {WhatKind} together with the {{:axiom}} attribute instead");
    } else if (!AutoGeneratedToken.Is(RangeToken) && Bodyless && !IsVirtual && !IsAbstract
                 && !this.IsExtern(resolver.Options) && !this.IsExplicitAxiom()) {
      foreach (var ensures in Ens) {
        if (!ensures.IsExplicitAxiom() && !resolver.Options.Get(CommonOptionBag.AllowAxioms)) {
          resolver.Reporter.Warning(MessageSource.Verifier, ResolutionErrors.ErrorId.none, ensures.Tok,
            $"This ensures clause is part of a bodyless {TypeName}. Add the {{:axiom}} attribute to it or the enclosing {TypeName} to suppress this warning");
        }
      }

    }
  }

  public bool HasPrecondition =>
    Req.Count > 0
    // The following check is incomplete, which is a bug.
    || Ins.Any(f => f.Type.AsSubsetType is not null);

  protected MethodOrFunction(RangeToken tok, Name name, bool hasStaticKeyword, bool isGhost, Attributes attributes, bool isRefining) : base(tok, name, hasStaticKeyword, isGhost, attributes, isRefining) {
  }

  public Specification<FrameExpression> Reads { get; set; }
}