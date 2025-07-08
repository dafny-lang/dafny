using System;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Server;
using System.Collections.Immutable;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Window;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  public class LspTelemetryPublisher : TelemetryPublisherBase {
    private readonly ILanguageServerFacade languageServer;

    public LspTelemetryPublisher(ILanguageServerFacade languageServer, ILogger<LspTelemetryPublisher> logger)
      : base(logger) {
      this.languageServer = languageServer;
    }

    public override void PublishTelemetry(ImmutableDictionary<string, object> data) {
      languageServer.Window.SendTelemetryEvent(new TelemetryEventParams {
        ExtensionData = data
      });
    }
  }
}