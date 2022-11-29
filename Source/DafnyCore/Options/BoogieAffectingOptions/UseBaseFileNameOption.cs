namespace Microsoft.Dafny;

public class UseBaseFileNameOption : BooleanOption {
  public static readonly UseBaseFileNameOption Instance = new();
  public override bool Hidden => true;
  public override string LongName => "useBaseNameForFileName";
  public override string ShortName => null;

  public override string Description => @"
When parsing use basename of file for tokens instead
of the path supplied on the command line".TrimStart();

  public override string PostProcess(DafnyOptions options) {
    options.UseBaseNameForFileName = Get(options);
    return null;
  }
}
