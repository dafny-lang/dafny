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
    public uint TimeLimit { get; set; } = 10;

    /// <summary>
    /// Gets or sets that may be used for verification. 0 = automatic.
    /// </summary>
    public uint Cores { get; set; } = 0;

    /// <summary>
    /// Gets or sets the number of snapshots to retain for caching of boogie. -1 disables snapshots.
    /// </summary>
    public int Snapshots { get; set; } = 3;
  }
}
