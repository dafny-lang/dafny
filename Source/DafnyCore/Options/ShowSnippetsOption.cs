namespace Microsoft.Dafny;

/// <summary>
/// This is an example of how to add an option that works for both the legacy and the new CLI UI.
/// </summary>
public class ShowSnippetsOption : BooleanOption, ILegacyOption {
  public static readonly ShowSnippetsOption Instance = new();

  public override string LongName => "show-snippets";
  public override string ShortName => null;
  public string Category => "Overall reporting and printing";
  public string LegacyName => "showSnippets";

  public override string Description => @"
0 (default) - Don't show source code snippets for Dafny messages.
1 - Show a source code snippet for each Dafny message.".TrimStart();

  public override string PostProcess(DafnyOptions options) {
    return null;
  }
}
