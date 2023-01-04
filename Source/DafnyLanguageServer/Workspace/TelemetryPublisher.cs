using System;
using Microsoft.Dafny.LanguageServer.Util;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Server;
using System.Collections.Generic;
using System.Linq;
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
      PublishTelemetry(ITelemetryPublisher.TelemetryEventKind.UnhandledException, e.ToString());
    }

    void ITelemetryPublisher.PublishTelemetry(ITelemetryPublisher.TelemetryEventKind kind, object? payload) {
      PublishTelemetry(kind, payload);
    }

    private void PublishTelemetry(ITelemetryPublisher.TelemetryEventKind kind, object? payload) {
      languageServer.Window.SendTelemetryEvent(new TelemetryEventParams {
        ExtensionData = new Dictionary<string, object> {
          {"kind", kind.ToString()},
          {"payload", payload ?? new Dictionary<string, object>()}
        }
      });
    }
  }
}