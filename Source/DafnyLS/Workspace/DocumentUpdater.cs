using DafnyLS.Language;
using DafnyLS.Language.Symbols;
using DafnyLS.Util;
using IntervalTree;
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

    public async Task<DafnyDocument> ApplyChangesAsync(DafnyDocument oldDocument, DidChangeTextDocumentParams documentChange, CancellationToken cancellationToken) {
      var mergedItem = new TextDocumentItem {
        LanguageId = oldDocument.Text.LanguageId,
        Uri = oldDocument.Uri,
        Version = documentChange.TextDocument.Version,
        Text = ApplyTextChanges(oldDocument.Text.Text, documentChange.ContentChanges, cancellationToken)
      };
      var loadedDocument = await _documentLoader.LoadAsync(mergedItem, cancellationToken);
      if(!loadedDocument.SymbolTable.Resolved) {
        return new DafnyDocument(
          loadedDocument.Text,
          loadedDocument.Errors,
          loadedDocument.Program,
          MigrateSymbolTable(oldDocument, documentChange.ContentChanges, cancellationToken)
        );
      }
      return loadedDocument;
    }

    private static string ApplyTextChanges(string originalText, Container<TextDocumentContentChangeEvent> changes, CancellationToken cancellationToken) {
      var mergedText = originalText;
      foreach(var change in changes) {
        cancellationToken.ThrowIfCancellationRequested();
        mergedText = ApplyTextChange(mergedText, change, cancellationToken);
      }
      return mergedText;
    }

    private static string ApplyTextChange(string originalText, TextDocumentContentChangeEvent change, CancellationToken cancellationToken) {
      if(change.Range == null) {
        // The property Range is null if a full document change was sent.
        return change.Text;
      }
      int absoluteStart = change.Range.Start.ToAbsolutePosition(originalText, cancellationToken);
      int absoluteEnd = change.Range.End.ToAbsolutePosition(originalText, cancellationToken);
      return originalText[..absoluteStart] + change.Text + originalText[absoluteEnd..];
    }

    private SymbolTable MigrateSymbolTable(DafnyDocument oldDocument, Container<TextDocumentContentChangeEvent> contentChanges, CancellationToken cancellationToken) {
      var migratedLookupTree = oldDocument.SymbolTable.LookupTree;
      var migratedDeclarations = oldDocument.SymbolTable.Locations;
      foreach(var change in contentChanges) {
        cancellationToken.ThrowIfCancellationRequested();
        migratedLookupTree = MigrateLookupTree(migratedLookupTree, change, cancellationToken);
        // TODO migrate the declarations
      }
      _logger.LogTrace("migrated the lookup tree, lookup before={}, after={}", oldDocument.SymbolTable.LookupTree.Count, migratedLookupTree.Count);
      return new SymbolTable(
        oldDocument.SymbolTable.CompilationUnit,
        oldDocument.SymbolTable.Declarations,
        migratedDeclarations,
        migratedLookupTree,
        true
      );
    }

    private IIntervalTree<Position, ILocalizableSymbol> MigrateLookupTree(IIntervalTree<Position, ILocalizableSymbol> lookupTree, TextDocumentContentChangeEvent change, CancellationToken cancellationToken) {
      var positionComparer = new PositionComparer();
      var migratedLookupTree = new IntervalTree<Position, ILocalizableSymbol>(positionComparer);
      var changeOffset = GetPositionAtEndOfAppliedChange(change, cancellationToken);
      foreach(var entry in lookupTree) {
        cancellationToken.ThrowIfCancellationRequested();
        if(IsDesignatorBeforeChange(positionComparer, change.Range, entry.To)) {
          migratedLookupTree.Add(entry.From, entry.To, entry.Value);
        }
        if(IsDesignatorAfterChange(positionComparer, change.Range, entry.From)) {
          // TODO adapt location
          var from = GetPositionWithOffset(entry.From, change.Range.End, changeOffset);
          var to = GetPositionWithOffset(entry.To, change.Range.End, changeOffset);
          migratedLookupTree.Add(from, to, entry.Value);
        }
      }
      return migratedLookupTree;
    }

    private Position GetPositionAtEndOfAppliedChange(TextDocumentContentChangeEvent change, CancellationToken cancellationToken) {
      var changeStart = change.Range.Start;
      var changeEof = change.Text.GetEofPosition(cancellationToken);
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
