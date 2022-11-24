namespace Microsoft.Dafny;

class WarnMissingConstructorParenthesisOption : BooleanOption {
  public static readonly WarnMissingConstructorParenthesisOption Instance = new();
  public override string LongName => "warn-missing-constructor-parentheses";

  public override string Description =>
    "Emits a warning when a constructor name in a case pattern is not followed by parentheses.";

  public override string PostProcess(DafnyOptions options) {
    options.DisallowConstructorCaseWithoutParentheses = Get(options);
    return null;
  }
}
