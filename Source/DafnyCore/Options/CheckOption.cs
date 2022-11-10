namespace Microsoft.Dafny;

public class CheckOption : BooleanOption {
  public static readonly CheckOption Instance = new();
  public override bool Hidden => false;
  public override string LongName => "check";
  public override string Description => @"
Instead of formatting files, verify that all files are already
formatted through and return a non-zero exit code if it is not the case".TrimStart();

  public override string PostProcess(DafnyOptions options) {
    options.FormatCheck = Get(options);
    return null;
  }
}
