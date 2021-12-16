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
    /// Gets or sets the time limit of the verifier (in seconds). 0 = no time limit
    /// </summary>
    public uint TimeLimit { get; set; } = 0;

    /// <summary>
    /// Gets or sets the number of cores that may be used for verification. 0 = automatic.
    /// </summary>
    public uint VcsCores { get; set; } = 0;

    /// <summary>
    /// Gets or sets the caching policy.
    /// </summary>
    public uint VerifySnapshots { get; set; } = 0;
  }
}
