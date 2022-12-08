namespace Microsoft.Dafny;

public class OptimizeErasableDatatypeWrapperOption : BooleanOption, ILegacyOption {
  public static readonly OptimizeErasableDatatypeWrapperOption Instance = new();

  public override string LongName => "optimize-erasable-datatype-wrapper";

  public override object DefaultValue => true;
  public string Category => "Compilation options";
  public string LegacyName => "optimizeErasableDatatypeWrapper";

  public override string Description => @"
0 - Include all non-ghost datatype constructors in the compiled code
1 (default) - In the compiled target code, transform any non-extern
    datatype with a single non-ghost constructor that has a single
    non-ghost parameter into just that parameter. For example, the type
        datatype Record = Record(x: int)
    is transformed into just 'int' in the target code.".TrimStart();

  public override string PostProcess(DafnyOptions options) {
    options.OptimizeErasableDatatypeWrappers = Get(options);
    return null;
  }
}
