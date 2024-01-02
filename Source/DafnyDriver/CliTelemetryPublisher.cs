using System;
using System.Collections.Immutable;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;

namespace DafnyDriver.Commands;

class CliTelemetryPublisher : ITelemetryPublisher {
  private readonly ILogger<ITelemetryPublisher> logger;

  public CliTelemetryPublisher(ILogger<ITelemetryPublisher> logger) {
    this.logger = logger;
  }

  public void PublishTelemetry(ImmutableDictionary<string, object> data) {
    // TODO throw new NotImplementedException();
  }

  // TODO make ITelemetryPublisher abstract class and move this there.
  public void PublishUnhandledException(Exception e) {
    logger.LogError(e, "exception occurred");
    PublishTelemetry(ImmutableDictionary.Create<string, object>().
      Add("kind", ITelemetryPublisher.TelemetryEventKind.UnhandledException).
      Add("payload", e.ToString()));
  }
}