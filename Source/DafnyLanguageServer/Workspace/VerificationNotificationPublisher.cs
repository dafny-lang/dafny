using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Server;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  public class VerificationNotificationPublisher : IVerificationNotificationPublisher {
    private readonly ITextDocumentLanguageServer _languageServer;

    public VerificationNotificationPublisher(ITextDocumentLanguageServer languageServer) {
      _languageServer = languageServer;
    }

    public void Started(TextDocumentItem textDocument) {
      _languageServer.SendNotification(new VerificationStartedParams {
        Uri = textDocument.Uri,
        Version = textDocument.Version,
      });
    }

    public void Completed(TextDocumentItem textDocument, bool verified) {
      _languageServer.SendNotification(new VerificationCompletedParams {
        Uri = textDocument.Uri,
        Version = textDocument.Version,
        Verified = verified
      });
    }
  }
}
