using Microsoft.Dafny.LanguageServer.Language;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Implementations of this interface are responsible to publish the diagnostics
  /// of a <see cref="Document"/> to the LSP client.
  /// </summary>
  public interface INotificationPublisher {
    /// <summary>
    /// Publishes the diagnostics of the specified dafny document to the connected LSP client.
    /// </summary>
    /// <param name="state">The document whose diagnostics should be published.</param>
    void PublishNotifications(IdeState previousState, IdeState state);

    /// <summary>
    /// Publishes the more precise real-time verification diagnostics to the connected LSP client
    /// </summary>
    void PublishGutterIcons(IdeState state, bool verificationStarted);

    /// <summary>
    /// Hides the previously published diagnostics of the specified dafny document.
    /// </summary>
    /// <param name="documentId">The ID document whose diagnostics should be hidden.</param>
    void HideDiagnostics(TextDocumentIdentifier documentId);
  }
}
