namespace Microsoft.Dafny;

public record ResolutionContext(ICodeContext CodeContext, bool IsTwoState, bool InOld, bool InReveal,
  bool InFunctionPostcondition, bool InFirstPhaseConstructor) {

  // Invariants:
  // InOld implies !IsTwoState
  // InFirstPhaseConstructor implies codeContext is Constructor

  public bool IsGhost => CodeContext.IsGhost;

  public ResolutionContext(ICodeContext codeContext, bool isTwoState)
    : this(codeContext, isTwoState, false, false, false, false) {
  }

  /// <summary>
  /// Return a ResolutionContext appropriate for the body of "codeContext".
  /// </summary>
  public static ResolutionContext FromCodeContext(ICodeContext codeContext) {
    bool isTwoState;
    if (codeContext is NoContext or DatatypeDecl or ConstantField) {
      isTwoState = false;
    } else if (codeContext is Function and not TwoStateFunction) {
      isTwoState = false;
    } else {
      isTwoState = true;
    }
    return new ResolutionContext(codeContext, isTwoState);
  }

  public IMethodCodeContext AsMethodCodeContext => CodeContext as IMethodCodeContext;

  public MethodOrConstructor AsMethod => CodeContext as MethodOrConstructor;

  public ResolutionContext WithGhost(bool isGhost) {
    if (CodeContext.IsGhost == isGhost) {
      return this;
    }
    return this with { CodeContext = new CodeContextWrapper(CodeContext, isGhost) };
  }
}