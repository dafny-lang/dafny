using System.Collections.Immutable;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;

namespace DafnyDriver.Commands;

class CliTelemetryPublisher : TelemetryPublisherBase {
  public CliTelemetryPublisher(ILogger<TelemetryPublisherBase> logger) : base(logger) {
  }

  public override void PublishTelemetry(ImmutableDictionary<string, object> data) {
  }
}