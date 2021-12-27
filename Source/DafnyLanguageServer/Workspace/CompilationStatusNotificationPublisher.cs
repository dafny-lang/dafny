using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Server;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  public class CompilationStatusNotificationPublisher : ICompilationStatusNotificationPublisher {
    private readonly ITextDocumentLanguageServer languageServer;

    public CompilationStatusNotificationPublisher(ITextDocumentLanguageServer languageServer) {
      this.languageServer = languageServer;
    }

    public void SendStatusNotification(TextDocumentItem textDocument, CompilationStatus status, string? message = null) {
      languageServer.SendNotification(new CompilationStatusParams {
        Uri = textDocument.Uri,
        Version = textDocument.Version,
        Status = status,
        Message = message
      });
    }
  }
}
