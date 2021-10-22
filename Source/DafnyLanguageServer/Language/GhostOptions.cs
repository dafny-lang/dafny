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
    /// Gets or sets whether the statements of ghost states should be faded out.
    /// </summary>
    public bool FadeStatements { get; set; }

    /// <summary>
    /// Gets whether any of the fade options is enabled.
    /// </summary>
    public bool FadeEnabled => FadeStatements;
  }
}
