namespace Microsoft.Dafny.LanguageServer.Language {
  /// <summary>
  /// Options for the resolution and compilation pipeline
  /// </summary>
  public class DafnyPluginsOptions {
    /// <summary>
    /// The IConfiguration section of the compiler options.
    /// </summary>
    public const string Section = "Dafny";

    /// <summary>
    /// Gets or sets which backends will be targeted so that their resolver can run before verification.
    /// </summary>
    public string Plugins { get; set; } = "";
  }
}
