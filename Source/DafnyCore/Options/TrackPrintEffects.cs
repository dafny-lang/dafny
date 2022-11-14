namespace Microsoft.Dafny; 

public class TrackPrintEffects : BooleanOption {
  public static readonly TrackPrintEffects Instance = new();
  public override string LongName => "track-print-effects";

  public override string Description => @"
false (default) - Every compiled method, constructor, and iterator,
   whether or not it bears a {{:print}} attribute, may have print
   effects.
true - A compiled method, constructor, or iterator is allowed to have
   print effects only if it is marked with {{:print}}.".TrimStart();

  public override string PostProcess(DafnyOptions options) {
    options.EnforcePrintEffects = Get(options);
    return null;
  }
}