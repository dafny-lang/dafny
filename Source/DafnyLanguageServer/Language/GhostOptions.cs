namespace Microsoft.Dafny.LanguageServer.Language {
  /// <summary>
  /// Options for the ghost state diagnostics.
  /// </summary>
  public class GhostOptions {
    /// <summary>
    /// The IConfiguration section of the ghost options.
    /// </summary>
    public const string Section = "Ghost";

    /// <summary>
    /// Gets or sets whether the statements of ghost states should be marked.
    /// </summary>
    public bool MarkStatements { get; set; } = true;
  }
}
