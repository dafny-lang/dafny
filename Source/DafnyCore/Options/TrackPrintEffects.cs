namespace Microsoft.Dafny; 

public class TrackPrintEffects : BooleanOption {
  public static readonly TrackPrintEffects Instance = new();
  public override string LongName => "track-print-effects";

  public override string Description =>
    "A compiled method, constructor, or iterator is allowed to have print effects only if it is marked with {{:print}}.";

  public override string PostProcess(DafnyOptions options) {
    options.EnforcePrintEffects = Get(options);
    return null;
  }
}
