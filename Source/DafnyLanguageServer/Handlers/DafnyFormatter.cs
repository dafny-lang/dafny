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
    var lastDocument = await documents.GetLastDocumentAsync(request.TextDocument.Uri);
    if (lastDocument != null) {
      var firstToken = lastDocument.Program.GetFirstTopLevelToken();
      string result;
      if (firstToken == null) {
        result = lastDocument.TextDocumentItem.Text;
      } else {
        result =
          Formatting.__default.printSourceReindent(firstToken,
            IndentationFormatter.ForProgram(lastDocument.Program));
      }

      return new TextEditContainer(new TextEdit[] {
        new TextEdit() {NewText = result, Range = lastDocument.TextDocumentItem.Range}
      });
    }

    return null;
  }
}