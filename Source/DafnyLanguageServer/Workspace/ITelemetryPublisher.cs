using System;
using System.Collections.Immutable;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Implementations of this interface are responsible to publish telemetry events
  /// of a <see cref="Compilation"/> to the LSP client.
  /// </summary>
  public interface ITelemetryPublisher {
    protected enum TelemetryEventKind {
      UpdateComplete,
      UnhandledException,
      SolverPath,
      Z3Version,
      Time
    }

    protected void PublishTelemetry(TelemetryEventKind kind, object? payload) {
      PublishTelemetry(kind.ToString(), ImmutableDictionary.Create<string, object>().Add("payload", payload!));
    }

    protected void PublishTelemetry(string kind, ImmutableDictionary<string, object> payload);

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

    public void PublishTime(string activity, string resource, TimeSpan span) {
      PublishTelemetry(TelemetryEventKind.Time, ImmutableDictionary.Create<string, object>().
        Add("activity", activity).Add("resource", resource).Add("time", span.TotalMilliseconds));
    }

    public void PublishZ3Version(string z3Version) {
      PublishTelemetry(TelemetryEventKind.Z3Version, z3Version);
    }
  }
}