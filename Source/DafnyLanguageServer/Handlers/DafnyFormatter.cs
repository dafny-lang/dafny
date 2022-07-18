using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Client.Capabilities;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Handlers; 

public class DafnyFormatter : DocumentFormattingHandlerBase {
  private readonly ILogger<DafnyCompletionHandler> logger;
  private readonly IDocumentDatabase documents;

  public DafnyFormatter(ILogger<DafnyCompletionHandler> logger, IDocumentDatabase documents) {
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
    if (documents.Documents.TryGetValue(request.TextDocument.Uri, out var documentEntry)) {
      var lastDocument = await documentEntry.LastDocument;
      var firstToken = lastDocument.Program.GetFirstTopLevelToken();
      var result = TokenFormatter.__default.printSourceReindent(firstToken, new DummyTokenIndentation());
      return new TextEditContainer(new TextEdit[] {
        new TextEdit() {NewText = result, Range = lastDocument.VerificationTree.Range}
      });
    }

    return null;
  }
}