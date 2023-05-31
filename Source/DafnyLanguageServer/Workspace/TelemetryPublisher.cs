using System;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Server;
using System.Collections.Immutable;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Window;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  public class TelemetryPublisher : ITelemetryPublisher {
    private readonly ILanguageServerFacade languageServer;
    private readonly ILogger<TelemetryPublisher> logger;

    public TelemetryPublisher(ILanguageServerFacade languageServer, ILogger<TelemetryPublisher> logger) {
      this.languageServer = languageServer;
      this.logger = logger;
    }

    public void PublishUnhandledException(Exception e) {
      logger.LogError(e, "exception occurred");
      PublishTelemetry(ITelemetryPublisher.TelemetryEventKind.UnhandledException.ToString(),
        ImmutableDictionary.Create<string, object>().Add("payload", e.ToString()));
    }

    public void PublishTelemetry(string kind, ImmutableDictionary<string, object> payload) {
      var data = payload.Add("kind", kind);
      languageServer.Window.SendTelemetryEvent(new TelemetryEventParams {
        ExtensionData = data
      });
    }
  }
}