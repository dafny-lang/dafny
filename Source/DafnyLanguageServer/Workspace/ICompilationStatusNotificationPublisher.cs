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
    /// <param name="compilation"></param>
    /// <param name="status"></param>
    /// <param name="message">Additional info about the current status</param>
    /// <param name="documentIdentifier"></param>
    void SendStatusNotification(Compilation compilation, CompilationStatus status, string? message = null);
  }
}
