namespace Microsoft.Dafny;

public class CoresOption : IntegerOption {
  public static readonly CoresOption Instance = new();
  public override object DefaultValue => 1;
  public override string LongName => "cores";
  public override string ShortName => null;
  public override string ArgumentName => "count";
  public override string Category => "General options";

  public override string Description => @"Run the Dafny CLI using <n> cores. Defaults to 1.";

  public override string PostProcess(DafnyOptions options) {
    options.VcsCores = Get(options);
    return null;
  }
}

public class UseBaseFileName : BooleanOption {
  public static readonly UseBaseFileName Instance = new();
  public override bool Hidden => true;
  public override string LongName => "useBaseNameForFileName";
  public override string ShortName => null;
  public override string Category => "General options";

  public override string Description => @"
When parsing use basename of file for tokens instead
of the path supplied on the command line".TrimStart();

  public override string PostProcess(DafnyOptions options) {
    options.UseBaseNameForFileName = Get(options);
    return null;
  }
}

public class VerificationTimeLimit : NaturalNumberOption {
  public static readonly VerificationTimeLimit Instance = new();
  public override object DefaultValue => 0U;
  public override string LongName => "verificationTimeLimit";
  public override string ShortName => null;
  public override string ArgumentName => "seconds";
  public override string Category => "Verification options";

  public override string Description => @"
Limit the number of seconds spent trying to verify
each procedure".TrimStart();

  public override string PostProcess(DafnyOptions options) {
    options.TimeLimit = Get(options);
    return null;
  }
}
