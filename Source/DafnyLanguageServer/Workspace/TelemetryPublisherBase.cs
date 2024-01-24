using System;
using System.Collections.Immutable;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Implementations of this interface are responsible to publish telemetry events
  /// of a <see cref="CompilationInput"/> to the LSP client.
  /// </summary>
  public abstract class TelemetryPublisherBase {
    protected ILogger<TelemetryPublisherBase> logger;

    protected enum TelemetryEventKind {
      UpdateComplete,
      UnhandledException,
      SolverPath,
      Z3Version,
      Time
    }

    protected TelemetryPublisherBase(ILogger<TelemetryPublisherBase> logger) {
      this.logger = logger;
    }

    protected void PublishTelemetry(TelemetryEventKind kind, object? payload) {
      PublishTelemetry(ImmutableDictionary.Create<string, object>().Add("kind", kind).Add("payload", payload!));
    }

    public abstract void PublishTelemetry(ImmutableDictionary<string, object> data);

    /// <summary>
    /// Signal the completion of a document update.
    /// </summary>
    public void PublishUpdateComplete() {
      PublishTelemetry(TelemetryEventKind.UpdateComplete, null);
    }

    public void PublishUnhandledException(Exception e) {
      logger.LogError(e, "exception occurred");
      PublishTelemetry(ImmutableDictionary.Create<string, object>().
        Add("kind", TelemetryPublisherBase.TelemetryEventKind.UnhandledException).
        Add("payload", e.ToString()));
    }

    public void PublishSolverPath(string solverPath) {
      PublishTelemetry(TelemetryEventKind.SolverPath, solverPath);
    }

    public void PublishCount(string activity, string resource, TimeSpan span) {
      PublishTelemetry(TelemetryEventKind.Time, ImmutableDictionary.Create<string, object>().
        Add("activity", activity).Add("resource", resource).Add("time", span.TotalMilliseconds));
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