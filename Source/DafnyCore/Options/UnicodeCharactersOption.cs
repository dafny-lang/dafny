namespace Microsoft.Dafny;

/// <summary>
/// This is an example of how to add an option that works for both the legacy and the new CLI UI.
/// </summary>
public class UnicodeCharactersOption : BooleanOption, ILegacyOption {
  public static readonly UnicodeCharactersOption Instance = new();

  public override string LongName => "unicode-char";
  public override string ShortName => null;
  public string LegacyName => "unicodeChar";
  public string Category => "Language feature selection";
  public override string Description => @"
0 (default) - The char type represents any UTF-16 code unit.
1 - The char type represents any Unicode scalar value.".TrimStart();

  public override string PostProcess(DafnyOptions options) {
    return null;
  }
}
