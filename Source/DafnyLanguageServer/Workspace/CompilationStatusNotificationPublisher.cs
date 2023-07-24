using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol.Server;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  public class CompilationStatusNotificationPublisher : ICompilationStatusNotificationPublisher {
    private readonly ITextDocumentLanguageServer languageServer;
    private readonly IProjectDatabase projectDatabase;

    public CompilationStatusNotificationPublisher(ITextDocumentLanguageServer languageServer, IProjectDatabase projectDatabase) {
      this.languageServer = languageServer;
      this.projectDatabase = projectDatabase;
    }

    public async Task SendStatusNotification(Compilation compilation, CompilationStatus status,
      string? message = null) {
      foreach (var uri in compilation.RootUris) {
        var uriProject = await projectDatabase.GetProject(uri);
        var ownedUri = uriProject.Equals(compilation.Project);
        if (ownedUri) {
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
}
