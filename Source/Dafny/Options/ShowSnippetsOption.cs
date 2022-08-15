namespace Microsoft.Dafny;

/// <summary>
/// This is an example of how to add an option that works for both the legacy and the new CLI UI.
/// </summary>
public class ShowSnippetsOption : BooleanOption {
  public static readonly ShowSnippetsOption Instance = new();

  public override string LongName => "showSnippets";
  public override string ShortName => null;
  public override string Category => "Overall reporting and printing";

  public override string Description => @"
0 (default) - don't show source code snippets for Dafny messages
1 - show a source code snippet for each Dafny message".TrimStart();
}