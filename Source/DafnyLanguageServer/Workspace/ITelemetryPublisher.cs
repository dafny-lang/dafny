using System;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Implementations of this interface are responsible to publish telemetry events
  /// of a <see cref="Document"/> to the LSP client.
  /// </summary>
  public interface ITelemetryPublisher {
    protected enum TelemetryEventKind {
      UpdateComplete,
      UnhandledException,
      SolverPath,
      Z3Version
    }

    /// <summary>
    /// Publish a telemetry event.
    /// </summary>
    /// <param name="kind">The kind of this telemetry event.</param>
    /// <param name="payload">The payload of this telemetry event.</param>
    protected void PublishTelemetry(TelemetryEventKind kind, object? payload);

    /// <summary>
    /// Signal the completion of a document update.
    /// </summary>
    public void PublishUpdateComplete() {
      PublishTelemetry(TelemetryEventKind.UpdateComplete, null);
    }

    /// <summary>
    /// Signal an unhandled error.
    /// </summary>
    public void PublishUnhandledException(Exception e);

    public void PublishSolverPath(string solverPath) {
      PublishTelemetry(TelemetryEventKind.SolverPath, solverPath);
    }

    public void PublishZ3Version(string z3Version) {
      PublishTelemetry(TelemetryEventKind.Z3Version, z3Version);
    }
  }
}