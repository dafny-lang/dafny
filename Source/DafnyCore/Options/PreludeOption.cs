namespace Microsoft.Dafny;

public class PreludeOption : StringOption, ILegacyOption {
  public static readonly PreludeOption Instance = new();
  public override object DefaultValue => null;
  public override string LongName => "prelude";
  public string LegacyName => "dprelude";
  public override string ArgumentName => "file";
  public string Category => "Input configuration";
  public override string Description => "Choose the Dafny prelude file.";

  public override string PostProcess(DafnyOptions options) {
    options.DafnyPrelude = Get(options);
    options.ExpandFilename(options.DafnyPrelude, x => options.DafnyPrelude = x, options.LogPrefix, options.FileTimestamp);
    return null;
  }
}
