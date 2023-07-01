using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Implementations of this interface are responsible to publish the compilation
  /// status of a <see cref="Compilation"/> to the LSP client.
  /// </summary>
  public interface ICompilationStatusNotificationPublisher {
    /// <summary>
    /// Sends the provided compilation status for the given document.
    /// </summary>
    /// <param name="documentIdentifier"></param>
    /// <param name="status"></param>
    /// <param name="message">Additional info about the current status</param>
    void SendStatusNotification(VersionedTextDocumentIdentifier documentIdentifier, CompilationStatus status,
      string? message = null);
  }
}
