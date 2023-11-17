using System.Threading.Tasks;
using System;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Implementations of this interface are responsible to publish the diagnostics
  /// of a <see cref="CompilationInput"/> to the LSP client.
  /// </summary>
  public interface INotificationPublisher {
    void PublishNotifications(IdeState previousState, IdeState state);
  }
}
