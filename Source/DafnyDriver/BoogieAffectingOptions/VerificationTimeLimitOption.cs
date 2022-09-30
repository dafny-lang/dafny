namespace Microsoft.Dafny;

public class VerificationTimeLimitOption : NaturalNumberOption {
  public static readonly VerificationTimeLimitOption Instance = new();
  public override object DefaultValue => 0U;
  public override string LongName => "verification-time-limit";
  public override string ShortName => null;
  public override string ArgumentName => "seconds";

  public override string Description => @"
Limit the number of seconds spent trying to verify
each procedure".TrimStart();

  public override string PostProcess(DafnyOptions options) {
    options.TimeLimit = Get(options);
    return null;
  }
}
