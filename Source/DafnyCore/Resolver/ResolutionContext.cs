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
    if (codeContext is NoContext || codeContext is DatatypeDecl || codeContext is ConstantField) {
      isTwoState = false;
    } else if (codeContext is Function && !(codeContext is TwoStateFunction)) {
      isTwoState = false;
    } else {
      isTwoState = true;
    }
    return new ResolutionContext(codeContext, isTwoState);
  }

  public IMethodCodeContext AsMethodCodeContext => CodeContext as IMethodCodeContext;

  public Method AsMethod => CodeContext as Method;

  public ResolutionContext WithGhost(bool isGhost) {
    if (CodeContext.IsGhost == isGhost) {
      return this;
    }
    return new ResolutionContext(new CodeContextWrapper(CodeContext, isGhost), IsTwoState, InOld, InReveal, InFunctionPostcondition, InFirstPhaseConstructor);
  }
}