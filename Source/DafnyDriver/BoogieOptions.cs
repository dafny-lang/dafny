namespace Microsoft.Dafny;

public class CoresOption : IntegerOption {
  public static readonly CoresOption Instance = new();
  public override object DefaultValue => 1;
  public override string LongName => "cores";
  public override string ShortName => null;

  public override string Description => @"
/cores:<n>
            Run the Dafny CLI using <n> cores. Defaults to 1.";

  public override void PostProcess(DafnyOptions options) {
    options.VcsCores = Get(options);
    base.PostProcess(options);
  }
}

public class UseBaseFileName : BooleanOption {
  public static readonly UseBaseFileName Instance = new();
  public override string LongName => "useBaseNameForFileName";
  public override string ShortName => null;
  public override string Description => @"
/useBaseNameForFileName : When parsing use basename of file for tokens instead
                          of the path supplied on the command line".TrimStart();

  public override void PostProcess(DafnyOptions options) {
    options.UseBaseNameForFileName = Get(options);
    base.PostProcess(options);
  }
}

public class VerificationTimeLimit : NaturalNumberOption {
  public static readonly VerificationTimeLimit Instance = new();
  public override object DefaultValue => 0;
  public override string LongName => "verificationTimeLimit";
  public override string ShortName => "";
  public override string Description => @"
/timeLimit:<num>
                Limit the number of seconds spent trying to verify
                each procedure".TrimStart();

  public override void PostProcess(DafnyOptions options) {
    options.TimeLimit = Get(options);
    base.PostProcess(options);
  }
}