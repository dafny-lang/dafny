using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Client.Capabilities;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Handlers;

public class DafnyFormattingHandler : DocumentFormattingHandlerBase {
  private readonly ILogger<DafnyFormattingHandler> logger;
  private readonly IProjectDatabase projects;

  public DafnyFormattingHandler(ILogger<DafnyFormattingHandler> logger, IProjectDatabase projects) {
    this.logger = logger;
    this.projects = projects;
  }

  protected override DocumentFormattingRegistrationOptions CreateRegistrationOptions(DocumentFormattingCapability capability,
    ClientCapabilities clientCapabilities) {
    return new DocumentFormattingRegistrationOptions() {
      DocumentSelector = DocumentSelector.ForLanguage("dafny")
    };
  }

  public override async Task<TextEditContainer?> Handle(DocumentFormattingParams request, CancellationToken cancellationToken) {
    var projectManager = await projects.GetProjectManager(request.TextDocument.Uri);
    if (projectManager == null) {
      return null;
    }
    var edits = await projectManager.CompilationManager.GetTextEditToFormatCode(request.TextDocument.Uri.ToUri());
    return edits;
  }
}