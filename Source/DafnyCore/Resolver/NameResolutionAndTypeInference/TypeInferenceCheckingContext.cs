namespace Microsoft.Dafny;

class TypeInferenceCheckingContext(IASTVisitorContext astVisitorContext) : IASTVisitorContext {
  public bool IsPrefixPredicate => astVisitorContext is PrefixPredicate;
  public bool IsExtremePredicate => astVisitorContext is ExtremePredicate;
  public bool IsPrefixDeclaration => astVisitorContext is PrefixPredicate or PrefixLemma;

  ModuleDefinition IASTVisitorContext.EnclosingModule => astVisitorContext.EnclosingModule;
}