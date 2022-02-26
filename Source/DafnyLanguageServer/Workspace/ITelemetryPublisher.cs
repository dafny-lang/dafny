using System;
using Microsoft.Dafny.LanguageServer.Language;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Implementations of this interface are responsible to publish telemetry events
  /// of a <see cref="DafnyDocument"/> to the LSP client.
  /// </summary>
  public interface ITelemetryPublisher {
    protected enum TelemetryEventKind {
      UpdateComplete,
      UnhandledException
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
    public void PublishUnhandledException(Exception e) {
      PublishTelemetry(TelemetryEventKind.UnhandledException, e.ToString());
    }
  }
}