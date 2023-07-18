using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Server;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  public class CompilationStatusNotificationPublisher : ICompilationStatusNotificationPublisher {
    private readonly ITextDocumentLanguageServer languageServer;

    public CompilationStatusNotificationPublisher(ITextDocumentLanguageServer languageServer) {
      this.languageServer = languageServer;
    }

    public void SendStatusNotification(Compilation compilation, CompilationStatus status,
      string? message = null) {
      foreach (var uri in compilation.RootUris) {
        languageServer.SendNotification(new CompilationStatusParams {
          Uri = uri,
          Version = compilation.Version,
          Status = status,
          Message = message
        });
      }
    }
  }
}
