namespace Microsoft.Dafny;

public class CheckOption : BooleanOption {
  public static readonly CheckOption Instance = new();
  public override bool Hidden => false;
  public override string LongName => "check";
  public override string Description => @"
Does not format files in place. Instead `dafny format --check` verifies
that all files are already formatted through `dafny format`
and return a non-zero exit code if it is not the case".TrimStart();

  public override string PostProcess(DafnyOptions options) {
    options.FormatCheck = Get(options);
    return null;
  }
}
