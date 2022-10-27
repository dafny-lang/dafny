namespace Microsoft.Dafny;

public class EnforceDeterminismOption : BooleanOption {
  public static readonly EnforceDeterminismOption Instance = new();

  public override string LongName => "enforce-determinism";

  public override string Description => @"
Check that only deterministic statements are used, so that
values seen during execution will be the same in every run of
the program.".TrimStart();

  public override string PostProcess(DafnyOptions options) {
    options.ForbidNondeterminism = Get(options);
    return null;
  }
}
