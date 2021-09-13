namespace Microsoft.Dafny.LanguageServer.Language {
  /// <summary>
  /// Options for the verifier.
  /// </summary>
  public class VerifierOptions {
    /// <summary>
    /// The IConfiguration section of the verifier options.
    /// </summary>
    public const string Section = "verifier";

    /// <summary>
    /// Gets or sets the time limit of the verifier.
    /// </summary>
    public uint TimeLimit { get; set; } = 0;
  }
}
