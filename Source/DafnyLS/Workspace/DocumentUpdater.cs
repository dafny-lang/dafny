using DafnyLS.Language;
using DafnyLS.Util;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;
using System.Threading.Tasks;

namespace DafnyLS.Workspace {
  public class DocumentUpdater : IDocumentUpdater {
    private readonly ILogger _logger;
    private readonly ITextDocumentLoader _documentLoader;

    public DocumentUpdater(ILogger<DocumentUpdater> logger, ITextDocumentLoader documentLoader) {
      _logger = logger;
      _documentLoader = documentLoader;
    }

    public Task<DafnyDocument> ApplyChangesAsync(DafnyDocument oldDocument, DidChangeTextDocumentParams documentChange, CancellationToken cancellationToken) {
      var mergedItem = new TextDocumentItem {
        LanguageId = oldDocument.Text.LanguageId,
        Uri = oldDocument.Uri,
        Version = documentChange.TextDocument.Version,
        Text = ApplyChanges(oldDocument.Text.Text, documentChange.ContentChanges, cancellationToken)
      };
      // TODO check if dafny could resolve the semantic model. If that's not the case, adapt the current symbol table according to the changes.
      return _documentLoader.LoadAsync(mergedItem, cancellationToken);
    }

    private static string ApplyChanges(string originalText, Container<TextDocumentContentChangeEvent> changes, CancellationToken cancellationToken) {
      var mergedText = originalText;
      foreach(var change in changes) {
        cancellationToken.ThrowIfCancellationRequested();
        mergedText = ApplyChanges(mergedText, change, cancellationToken);
      }
      return mergedText;
    }

    private static string ApplyChanges(string originalText, TextDocumentContentChangeEvent change, CancellationToken cancellationToken) {
      if(change.Range == null) {
        // The property Range is null if a full document change was sent.
        return change.Text;
      }
      int absoluteStart = change.Range.Start.ToAbsolutePosition(originalText, cancellationToken);
      int absoluteEnd = change.Range.End.ToAbsolutePosition(originalText, cancellationToken);
      return originalText[..absoluteStart] + change.Text + originalText[absoluteEnd..];
    }
  }
}
