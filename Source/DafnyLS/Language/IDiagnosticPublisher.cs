using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Language {
  /// <summary>
  /// Implementations of this interface are responsible to publish the diagnostics
  /// of a <see cref="DafnyDocument"/> to the LSP client.
  /// </summary>
  public interface IDiagnosticPublisher {
    /// <summary>
    /// Publishes the diagnostics of the specified dafny document to the connected LSP client.
    /// </summary>
    /// <param name="document">The document whose diagnostics should be published.</param>
    void PublishDiagnostics(DafnyDocument document, CancellationToken cancellationToken);
  }
}
