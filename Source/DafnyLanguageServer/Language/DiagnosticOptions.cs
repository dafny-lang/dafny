using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Language {
  /// <summary>
  /// Options for diagnostics reported to the LSP client.
  /// </summary>
  public class DiagnosticOptions {
    /// <summary>
    /// The IConfiguration section of the document options.
    /// </summary>
    public const string Section = "Diagnostic";

    /// <summary>
    /// Gets or sets the severity of info messages produced by the Dafny compiler.
    /// </summary>
    public DiagnosticSeverity InfoSeverity { get; set; } = DiagnosticSeverity.Information;
  }
}
