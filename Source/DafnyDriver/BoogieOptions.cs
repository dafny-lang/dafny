namespace Microsoft.Dafny;

public class HelpOption : BooleanOption {
  public static readonly HelpOption Instance = new();
  public override string LongName => "help";
  public override string ShortName => null;
  public override string Category => "General options";
  public override string Description => "Display this help text";

  public override string TypedPostProcess(DafnyOptions options, bool value) {
    options.HelpRequested = Get(options);
    return base.TypedPostProcess(options, value);
  }
}

public class CoresOption : IntegerOption {
  public static readonly CoresOption Instance = new();
  public override object DefaultValue => 1;
  public override string LongName => "cores";
  public override string ShortName => null;
  public override string ArgumentName => "count";
  public override string Category => "General options";

  public override string Description => @"Run the Dafny CLI using <n> cores. Defaults to 1.";

  public override string TypedPostProcess(DafnyOptions options, int value) {
    options.VcsCores = value;
    return base.TypedPostProcess(options, value);
  }
}

public class UseBaseFileName : BooleanOption {
  public static readonly UseBaseFileName Instance = new();
  public override string LongName => "useBaseNameForFileName";
  public override string ShortName => null;
  public override string Category => "General options";

  public override string Description => @"
When parsing use basename of file for tokens instead
of the path supplied on the command line".TrimStart();

  public override string TypedPostProcess(DafnyOptions options, bool value) {
    options.UseBaseNameForFileName = value;
    return base.TypedPostProcess(options, value);
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

  public override string TypedPostProcess(DafnyOptions options, uint value) {
    options.TimeLimit = value;
    return base.TypedPostProcess(options, value);
  }
}
