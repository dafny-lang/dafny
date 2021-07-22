using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Server;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  public class CompilationStatusNotificationPublisher : ICompilationStatusNotificationPublisher {
    private readonly ITextDocumentLanguageServer _languageServer;

    public CompilationStatusNotificationPublisher(ITextDocumentLanguageServer languageServer) {
      _languageServer = languageServer;
    }

    public void SendStatusNotification(TextDocumentItem textDocument, CompilationStatus status) {
      _languageServer.SendNotification(new CompilationStatusParams {
        Uri = textDocument.Uri,
        Version = textDocument.Version,
        Status = status
      });
    }
  }
}
