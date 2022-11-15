namespace Microsoft.Dafny;

public class NonZeroExitCodeIfErrorsOption : BooleanOption {
  public static readonly NonZeroExitCodeIfErrorsOption Instance = new();
  public override object DefaultValue => true;
  public override string LongName => "nonzero-exit-code-if-errors";
  public override string ShortName => null;
  public override string ArgumentName => "boolean";

  public override string Description => @"
if false then always exit with a 0 exit code, regardless of whether errors are found.
If true (default) then use the appropriate exit code.".TrimStart();

  public override string PostProcess(DafnyOptions options) {
    options.CountVerificationErrors = Get(options);
    return null;
  }
}
