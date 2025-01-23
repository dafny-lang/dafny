using System.Collections.Immutable;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;

namespace DafnyDriver.Commands;

class CliTelemetryPublisher(ILogger<TelemetryPublisherBase> logger) : TelemetryPublisherBase(logger) {
  public override void PublishTelemetry(ImmutableDictionary<string, object> data) {
  }
}