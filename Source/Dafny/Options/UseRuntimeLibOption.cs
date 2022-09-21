using Microsoft.Boogie;

namespace Microsoft.Dafny;

public class UseRuntimeLibOption : BooleanOption {
  public static readonly UseRuntimeLibOption Instance = new();
  public override string LongName => "useRuntimeLib";
  public override string Category => "Compilation options";

  public override string Description => @"
Refer to pre-built DafnyRuntime.dll in compiled assembly rather
than including DafnyRuntime.cs verbatim.".TrimStart();

  public override void Parse(CommandLineParseState ps, DafnyOptions options) {
    Set(options, true);
  }
  public override string PostProcess(DafnyOptions options) {
    options.UseRuntimeLib = Get(options);
    return null;
  }
}

public class IncludeRuntimeOption : BooleanOption {
  public static readonly IncludeRuntimeOption Instance = new();
  public override string LongName => "include-runtime";
  public override string Category => "Compilation options";

  public override string Description => @"Include the Dafny runtime as source in the target language.".TrimStart();

  public override void Parse(CommandLineParseState ps, DafnyOptions options) {
    Set(options, true);
  }
  public override string PostProcess(DafnyOptions options) {
    options.UseRuntimeLib = !Get(options);
    return null;
  }
}