using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace.ChangeProcessors;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Options;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  public class DocumentUpdater : IDocumentUpdater {
    private readonly ILogger logger;
    private readonly DocumentOptions options;
    private readonly ITextChangeProcessor textChangeProcessor;
    private readonly ISymbolTableRelocator symbolTableRelocator;
    private readonly ITextDocumentLoader documentLoader;

    private bool Verify => options.Verify == AutoVerification.OnChange;

    public DocumentUpdater(
      ILogger<DocumentUpdater> logger,
      IOptions<DocumentOptions> options,
      ITextChangeProcessor textChangeProcessor,
      ISymbolTableRelocator symbolTableRelocator,
      ITextDocumentLoader documentLoader
    ) {
      this.logger = logger;
      this.options = options.Value;
      this.textChangeProcessor = textChangeProcessor;
      this.symbolTableRelocator = symbolTableRelocator;
      this.documentLoader = documentLoader;
    }

    public async Task<DafnyDocument> ApplyChangesAsync(DafnyDocument oldDocument, DidChangeTextDocumentParams documentChange, CancellationToken cancellationToken) {
      // We do not pass the cancellation token to the text change processor because the text has to be kept in sync with the LSP client.
      var updatedText = textChangeProcessor.ApplyChange(oldDocument.Text, documentChange, CancellationToken.None);
      try {
        var newDocument = await documentLoader.LoadAsync(updatedText, Verify, cancellationToken);
        if (newDocument.SymbolTable.Resolved) {
          return newDocument;
        }
        // The document loader failed to create a new symbol table. Since we'd still like to provide
        // features such as code completion and lookup, we re-locate the previously resolved symbols
        // according to the change.
        return newDocument with {
          SymbolTable = symbolTableRelocator.Relocate(oldDocument.SymbolTable, documentChange, CancellationToken.None)
        };
      } catch (System.OperationCanceledException) {
        // The document load was canceled before it could complete. We migrate the document
        // to re-locate symbols that were resolved previously.
        logger.LogTrace("document loading canceled, applying migration");
        return oldDocument with {
          Text = updatedText,
          SymbolTable = symbolTableRelocator.Relocate(oldDocument.SymbolTable, documentChange, CancellationToken.None),
          SerializedCounterExamples = null,
          LoadCanceled = true
        };
      }
    }
  }
}
