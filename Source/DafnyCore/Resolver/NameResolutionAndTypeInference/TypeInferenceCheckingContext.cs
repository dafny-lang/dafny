namespace Microsoft.Dafny;

class TypeInferenceCheckingContext : IASTVisitorContext {
  private readonly IASTVisitorContext astVisitorContext;

  public bool IsPrefixPredicate => astVisitorContext is PrefixPredicate;
  public bool IsExtremePredicate => astVisitorContext is ExtremePredicate;
  public bool IsPrefixDeclaration => astVisitorContext is PrefixPredicate or PrefixLemma;

  public TypeInferenceCheckingContext(IASTVisitorContext astVisitorContext) {
    this.astVisitorContext = astVisitorContext;
  }

  ModuleDefinition IASTVisitorContext.EnclosingModule => astVisitorContext.EnclosingModule;
}