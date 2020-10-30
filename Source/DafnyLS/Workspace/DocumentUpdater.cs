using IntervalTree;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Util;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  public class DocumentUpdater : IDocumentUpdater {
    private readonly ILogger _logger;
    private readonly ITextDocumentLoader _documentLoader;

    public DocumentUpdater(ILogger<DocumentUpdater> logger, ITextDocumentLoader documentLoader) {
      _logger = logger;
      _documentLoader = documentLoader;
    }

    public async Task<DafnyDocument> ApplyChangesAsync(DafnyDocument oldDocument, DidChangeTextDocumentParams documentChange, CancellationToken cancellationToken) {
      var changeProcessor = new ChangeProcessor(_logger, oldDocument, documentChange.ContentChanges, cancellationToken);
      var mergedItem = new TextDocumentItem {
        LanguageId = oldDocument.Text.LanguageId,
        Uri = oldDocument.Uri,
        Version = documentChange.TextDocument.Version,
        Text = changeProcessor.MigrateText()
      };
      var loadedDocument = await _documentLoader.LoadAsync(mergedItem, cancellationToken);
      if(!loadedDocument.SymbolTable.Resolved) {
        return new DafnyDocument(
          loadedDocument.Text,
          loadedDocument.Errors,
          loadedDocument.Program,
          changeProcessor.MigrateSymbolTable()
        );
      }
      return loadedDocument;
    }

    private class ChangeProcessor {
      private readonly ILogger _logger;
      private readonly DafnyDocument _originalDocument;
      private readonly Container<TextDocumentContentChangeEvent> _contentChanges;
      private readonly CancellationToken _cancellationToken;

      public ChangeProcessor(ILogger logger, DafnyDocument originalDocument, Container<TextDocumentContentChangeEvent> contentChanges, CancellationToken cancellationToken) {
        _logger = logger;
        _originalDocument = originalDocument;
        _contentChanges = contentChanges;
        _cancellationToken = cancellationToken;
      }

      public string MigrateText() {
        var mergedText = _originalDocument.Text.Text;
        foreach(var change in _contentChanges) {
          _cancellationToken.ThrowIfCancellationRequested();
          mergedText = ApplyTextChange(mergedText, change);
        }
        return mergedText;
      }

      private string ApplyTextChange(string previousText, TextDocumentContentChangeEvent change) {
        if(change.Range == null) {
          // The property Range is null if a full document change was sent.
          return change.Text;
        }
        int absoluteStart = change.Range.Start.ToAbsolutePosition(previousText, _cancellationToken);
        int absoluteEnd = change.Range.End.ToAbsolutePosition(previousText, _cancellationToken);
        return previousText[..absoluteStart] + change.Text + previousText[absoluteEnd..];
      }

      public SymbolTable MigrateSymbolTable() {
        var migratedLookupTree = _originalDocument.SymbolTable.LookupTree;
        var migratedDeclarations = _originalDocument.SymbolTable.Locations;
        foreach(var change in _contentChanges) {
          _cancellationToken.ThrowIfCancellationRequested();
          var afterChangeEndOffset = GetPositionAtEndOfAppliedChange(change);
          migratedLookupTree = ApplyLookupTreeChange(migratedLookupTree, change, afterChangeEndOffset);
          // TODO migrate the declarations
        }
        _logger.LogTrace("migrated the lookup tree, lookup before={}, after={}", _originalDocument.SymbolTable.LookupTree.Count, migratedLookupTree.Count);
        return new SymbolTable(
          _originalDocument.SymbolTable.CompilationUnit,
          _originalDocument.SymbolTable.Declarations,
          migratedDeclarations,
          migratedLookupTree,
          true
        );
      }

      private IIntervalTree<Position, ILocalizableSymbol> ApplyLookupTreeChange(
          IIntervalTree<Position, ILocalizableSymbol> previousLookupTree, TextDocumentContentChangeEvent change, Position afterChangeEndOffset
      ) {
        var positionComparer = new PositionComparer();
        var migratedLookupTree = new IntervalTree<Position, ILocalizableSymbol>(positionComparer);
        foreach(var entry in previousLookupTree) {
          _cancellationToken.ThrowIfCancellationRequested();
          if(IsDesignatorBeforeChange(positionComparer, change.Range, entry.To)) {
            migratedLookupTree.Add(entry.From, entry.To, entry.Value);
          }
          if(IsDesignatorAfterChange(positionComparer, change.Range, entry.From)) {
            // TODO adapt location
            var beforeChangeEndOffset = change.Range.End;
            var from = GetPositionWithOffset(entry.From, beforeChangeEndOffset, afterChangeEndOffset);
            var to = GetPositionWithOffset(entry.To, beforeChangeEndOffset, afterChangeEndOffset);
            migratedLookupTree.Add(from, to, entry.Value);
          }
        }
        return migratedLookupTree;
      }

      private Position GetPositionAtEndOfAppliedChange(TextDocumentContentChangeEvent change) {
        var changeStart = change.Range.Start;
        var changeEof = change.Text.GetEofPosition(_cancellationToken);
        var characterOffset = changeEof.Character;
        if(changeEof.Line == 0) {
          characterOffset = changeStart.Character + changeEof.Character;
        }
        return new Position(changeStart.Line + changeEof.Line, characterOffset);
      }

      private Position GetPositionWithOffset(Position position, Position originalOffset, Position changeOffset) {
        int newLine = position.Line - originalOffset.Line + changeOffset.Line;
        int newCharacter = position.Character;
        if(newLine == changeOffset.Line) {
          // The end of the change occured within the line of the given position.
          newCharacter = position.Character - originalOffset.Character + changeOffset.Character;
        }
        return new Position(newLine, newCharacter);
      }

      private bool IsDesignatorBeforeChange(PositionComparer comparer, Range changeRange, Position symbolTo) {
        return comparer.Compare(symbolTo, changeRange.Start) <= 0;
      }

      private bool IsDesignatorAfterChange(PositionComparer comparer, Range changeRange, Position symbolFrom) {
        return comparer.Compare(symbolFrom, changeRange.End) >= 0;
      }
    }
  }
}
