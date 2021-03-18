using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Server;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  public class VerificationNotificationPublisher : IVerificationNotificationPublisher {
    private readonly ILanguageServer _languageServer;

    public VerificationNotificationPublisher(ILanguageServer languageServer) {
      _languageServer = languageServer;
    }

    public void Started(TextDocumentItem textDocument) {
      _languageServer.SendNotification(new VerificationStartedParams(textDocument.Uri, textDocument.Version));
    }

    public void Completed(TextDocumentItem textDocument, bool verified) {
      _languageServer.SendNotification(new VerificationCompletedParams(textDocument.Uri, textDocument.Version, verified));
    }
  }
}
