namespace Microsoft.Dafny;

public abstract class MethodOrFunction : MemberDecl {
  protected abstract bool Bodyless { get; }
  protected abstract string TypeName { get; }

  public bool IsVirtual => EnclosingClass is TraitDecl && !IsStatic;

  public virtual void Resolve(Resolver resolver) {
    if (Bodyless && !IsVirtual) {
      var mayBeAxiom = this.IsExplicitAxiom() || this.IsExtern();
      if (!resolver.Options.Get(CommonOptionBag.AllowAxioms) && !mayBeAxiom) {
        resolver.Reporter.Warning(MessageSource.Resolver, ErrorDetail.ErrorID.None, Tok, $"{TypeName.CapitaliseFirstLetter()} {FullName} has no body. Add the {{:axiom}} attribute to it to suppress this warning.");
      }
    }
  }

  protected MethodOrFunction(RangeToken tok, Name name, bool hasStaticKeyword, bool isGhost, Attributes attributes, bool isRefining) : base(tok, name, hasStaticKeyword, isGhost, attributes, isRefining) {
  }
}