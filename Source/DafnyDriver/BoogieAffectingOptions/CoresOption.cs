namespace Microsoft.Dafny;

public class CoresOption : IntegerOption {
  public static readonly CoresOption Instance = new();
  public override object DefaultValue => 1;
  public override string LongName => "cores";
  public override string ShortName => null;
  public override string ArgumentName => "count";

  public override string Description => @"Run the Dafny CLI using <n> cores. Defaults to 1.";

  public override string PostProcess(DafnyOptions options) {
    options.VcsCores = Get(options);
    return null;
  }
}
