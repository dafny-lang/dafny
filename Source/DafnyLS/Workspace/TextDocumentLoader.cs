using DafnyLS.Language;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;
using System.Threading.Tasks;

namespace DafnyLS.Workspace {
  internal class TextDocumentLoader : ITextDocumentLoader {
    private readonly IDafnyParser _parser;

    public TextDocumentLoader(IDafnyParser parser) {
      _parser = parser;
    }

    public async Task<DafnyDocument> LoadAsync(TextDocumentItem textDocument, CancellationToken cancellationToken) {
      var errorReporter = new BuildErrorReporter();
      var program = await _parser.ParseAsync(textDocument, errorReporter, cancellationToken);
      return new DafnyDocument(textDocument, errorReporter, program);
    }
  }
}
