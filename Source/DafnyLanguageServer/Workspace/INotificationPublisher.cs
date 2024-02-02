using System.Threading.Tasks;
using System;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Implementations of this interface are responsible to publish the diagnostics
  /// of a <see cref="CompilationInput"/> to the LSP client.
  /// </summary>
  public interface INotificationPublisher {
    /// <summary>
    /// Publishes the diagnostics of the specified dafny document to the connected LSP client.
    /// </summary>
    void PublishNotifications(IdeState previousState, IdeState state);
  }
}
