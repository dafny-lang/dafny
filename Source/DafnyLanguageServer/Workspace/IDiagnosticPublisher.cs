using Microsoft.Dafny.LanguageServer.Language;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Implementations of this interface are responsible to publish the diagnostics
  /// of a <see cref="DafnyDocument"/> to the LSP client.
  /// </summary>
  public interface IDiagnosticPublisher {
    /// <summary>
    /// Publishes the diagnostics of the specified dafny document to the connected LSP client.
    /// </summary>
    /// <param name="document">The document whose diagnostics should be published.</param>
    void PublishDiagnostics(DafnyDocument document);

    /// <summary>
    /// Hides the previously published diagnostics of the specified dafny document.
    /// </summary>
    /// <param name="documentId">The ID document whose diagnostics should be hidden.</param>
    void HideDiagnostics(TextDocumentIdentifier documentId);
  }
}
