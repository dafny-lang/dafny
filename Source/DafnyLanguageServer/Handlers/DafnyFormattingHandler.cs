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
  private readonly ILogger<DafnyCompletionHandler> logger;
  private readonly IDocumentDatabase documents;

  public DafnyFormattingHandler(ILogger<DafnyCompletionHandler> logger, IDocumentDatabase documents) {
    this.logger = logger;
    this.documents = documents;
  }

  protected override DocumentFormattingRegistrationOptions CreateRegistrationOptions(DocumentFormattingCapability capability,
    ClientCapabilities clientCapabilities) {
    return new DocumentFormattingRegistrationOptions() {
      DocumentSelector = DocumentSelector.ForLanguage("dafny")
    };
  }

  public override async Task<TextEditContainer?> Handle(DocumentFormattingParams request, CancellationToken cancellationToken) {
    var documentManager = documents.GetDocumentManager(request.TextDocument.Uri);
    if (documentManager == null) {
      return null;
    }
    var edits = await documentManager.Compilation.GetTextEditToFormatCode();
    return edits;
  }
}