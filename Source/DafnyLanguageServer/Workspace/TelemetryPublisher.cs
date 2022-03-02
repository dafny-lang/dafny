using Microsoft.Dafny.LanguageServer.Util;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Server;
using System.Collections.Generic;
using System.Linq;
using OmniSharp.Extensions.LanguageServer.Protocol.Window;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  public class TelemetryPublisher : ITelemetryPublisher {
    private readonly ILanguageServerFacade languageServer;

    public TelemetryPublisher(ILanguageServerFacade languageServer) {
      this.languageServer = languageServer;
    }

    void ITelemetryPublisher.PublishTelemetry(ITelemetryPublisher.TelemetryEventKind kind, object? payload) {
      languageServer.Window.SendTelemetryEvent(new TelemetryEventParams {
        ExtensionData = new Dictionary<string, object> {
          {"kind", kind.ToString()},
          {"payload", payload ?? new Dictionary<string, object>()}
        }
      });
    }
  }
}