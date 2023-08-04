using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Implementations of this interface are responsible to publish the compilation
  /// status of a <see cref="Compilation"/> to the LSP client.
  /// </summary>
  public interface ICompilationStatusNotificationPublisher {
    Task SendStatusNotification(Compilation compilation, CompilationStatus status, string? message = null);
  }
}
