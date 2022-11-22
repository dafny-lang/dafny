namespace Microsoft.Dafny;

public class EnforceDeterminismOption : BooleanOption {
  public static readonly EnforceDeterminismOption Instance = new();

  public override string LongName => "enforce-determinism";

  public override string Description => "Check that only deterministic statements are used, so that values seen during execution will be the same in every run of the program.".TrimStart();

  public override string PostProcess(DafnyOptions options) {
    options.ForbidNondeterminism = Get(options);
    options.DefiniteAssignmentLevel = Get(options) ? 2 : 1;
    return null;
  }
}

public class RelaxDefiniteAssignment : BooleanOption {
  public static readonly RelaxDefiniteAssignment Instance = new();
  public override string LongName => "relax-definite-assignment";

  public override string Description =>
    "Allow variables to be read before they are assigned, but only if they have an auto-initializable type or if they are ghost and have a nonempty type.";

  public override string PostProcess(DafnyOptions options) {
    if (Get(options) && options.ForbidNondeterminism) {
      return $"The option {LongName} can not be used in conjunction with {EnforceDeterminismOption.Instance.LongName}.";
    }
    options.DefiniteAssignmentLevel = Get(options) ? 1 : 2;
    return null;
  }
}
