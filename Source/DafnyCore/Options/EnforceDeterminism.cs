namespace Microsoft.Dafny;

public class EnforceDeterminism : BooleanOption {
  public static readonly EnforceDeterminism Instance = new();

  public override string LongName => "enforce-determinism";

  public override string Description => @"
Check that no nondeterministic statements are used, so that
values seen during execution will be the same in every run of
the program.".TrimStart();

  public override string PostProcess(DafnyOptions options) {
    options.ForbidNondeterminism = Get(options);
  }
}
