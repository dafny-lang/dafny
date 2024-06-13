namespace Microsoft.Dafny;

public record ResolutionContext(ICodeContext CodeContext, bool IsTwoState, bool InOld, bool InReveal,
  bool InFunctionPostcondition, bool InFirstPhaseConstructor, bool InBlindMethod) {

  // Invariants:
  // InOld implies !IsTwoState
  // InFirstPhaseConstructor implies codeContext is Constructor

  public bool IsGhost => CodeContext.IsGhost;

  public ResolutionContext(ICodeContext codeContext, bool isTwoState)
    : this(codeContext, isTwoState, false, false, false, false, false) {
  }

  /// <summary>
  /// Return a ResolutionContext appropriate for the body of "codeContext".
  /// </summary>
  public static ResolutionContext FromCodeContext(ICodeContext codeContext) {
    var isBlind = codeContext is Method method && method.IsBlind;
    bool isTwoState;
    if (codeContext is NoContext || codeContext is DatatypeDecl || codeContext is ConstantField) {
      isTwoState = false;
    } else if (codeContext is Function && !(codeContext is TwoStateFunction)) {
      isTwoState = false;
    } else {
      isTwoState = true;
    }
    return new ResolutionContext(codeContext, isTwoState) {
      InBlindMethod = isBlind
    };
  }

  public IMethodCodeContext AsMethodCodeContext => CodeContext as IMethodCodeContext;

  public Method AsMethod => CodeContext as Method;

  public ResolutionContext WithGhost(bool isGhost) {
    if (CodeContext.IsGhost == isGhost) {
      return this;
    }
    return this with { CodeContext = new CodeContextWrapper(CodeContext, isGhost) };
  }
}