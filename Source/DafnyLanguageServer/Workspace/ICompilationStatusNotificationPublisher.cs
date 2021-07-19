using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Implementations of this interface are responsible to publish the compilation
  /// status of a <see cref="DafnyDocument"/> to the LSP client.
  /// </summary>
  public interface ICompilationStatusNotificationPublisher {
    /// <summary>
    /// Sends the provided compilation status for the given document.
    /// </summary>
    /// <param name="textDocument">The document which had a compilation status change.</param>
    /// <param name="status"></param>
    void SendStatusNotification(TextDocumentItem textDocument, CompilationStatus status);
  }
}
