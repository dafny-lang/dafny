namespace Microsoft.Dafny;

public class WarningsAsErrorsOption : BooleanOption {
  public static readonly WarningsAsErrorsOption Instance = new();

  public override string LongName => "warnings-as-errors";

  public override string Description => "Treat warnings as errors.";

  public override string PostProcess(DafnyOptions options) {
    options.WarningsAsErrors = Get(options);
    return null;
  }
}
