namespace Microsoft.Dafny;

class WarningAsErrorsOption : BooleanOption {
  public static readonly WarningAsErrorsOption Instance = new();
  public override string LongName => "warn-as-errors";
  public override string Description => "Treat warnings as errors.";

  public override string PostProcess(DafnyOptions options) {
    options.WarningsAsErrors = Get(options);
    return null;
  }
}
