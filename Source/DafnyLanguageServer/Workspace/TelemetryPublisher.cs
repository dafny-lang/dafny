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
      PublishTelemetry(ImmutableDictionary.Create<string, object>().
          Add("kind", ITelemetryPublisher.TelemetryEventKind.UnhandledException).
          Add("payload", e.ToString()));
    }

    public void PublishTelemetry(ImmutableDictionary<string, object> data) {
      languageServer.Window.SendTelemetryEvent(new TelemetryEventParams {
        ExtensionData = data
      });
    }
  }
}