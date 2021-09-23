using IntervalTree;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Util;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Options;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  public class DocumentUpdater : IDocumentUpdater {
    private readonly ILogger _logger;
    private readonly DocumentOptions _options;
    private readonly ITextDocumentLoader _documentLoader;

    private bool Verify => _options.Verify == AutoVerification.OnChange;

    public DocumentUpdater(ILogger<DocumentUpdater> logger, IOptions<DocumentOptions> options, ITextDocumentLoader documentLoader) {
      _logger = logger;
      _options = options.Value;
      _documentLoader = documentLoader;
    }

    public async Task<DafnyDocument> ApplyChangesAsync(DafnyDocument oldDocument, DidChangeTextDocumentParams documentChange, CancellationToken cancellationToken) {
      var changeProcessor = new ChangeProcessor(_logger, oldDocument, documentChange.ContentChanges);
      var mergedItem = new TextDocumentItem {
        LanguageId = oldDocument.Text.LanguageId,
        Uri = oldDocument.Uri,
        Version = documentChange.TextDocument.Version,
        Text = changeProcessor.MigrateText()
      };

      DafnyDocument? newDocument;
      try {
        newDocument = await _documentLoader.LoadAsync(mergedItem, Verify, cancellationToken);
      } catch (System.OperationCanceledException) {
        _logger.LogTrace("document loading canceled, applying migration");
        newDocument = oldDocument;
      }
      if (!newDocument.SymbolTable.Resolved) {
        return new DafnyDocument(
          mergedItem,
          newDocument.Errors,
          newDocument.Program,
          changeProcessor.MigrateSymbolTable(),
          serializedCounterExamples: null
        );
      }
      return newDocument;
    }

    private class ChangeProcessor {
      private readonly ILogger _logger;
      private readonly DafnyDocument _originalDocument;
      private readonly Container<TextDocumentContentChangeEvent> _contentChanges;

      public ChangeProcessor(ILogger logger, DafnyDocument originalDocument, Container<TextDocumentContentChangeEvent> contentChanges) {
        _logger = logger;
        _originalDocument = originalDocument;
        _contentChanges = contentChanges;
      }

      public string MigrateText() {
        var mergedText = _originalDocument.Text.Text;
        foreach (var change in _contentChanges) {
          mergedText = ApplyTextChange(mergedText, change);
        }
        return mergedText;
      }

      private string ApplyTextChange(string previousText, TextDocumentContentChangeEvent change) {
        if (change.Range == null) {
          throw new System.InvalidOperationException("the range of the change must not be null");
        }
        int absoluteStart = change.Range.Start.ToAbsolutePosition(previousText);
        int absoluteEnd = change.Range.End.ToAbsolutePosition(previousText);
        return previousText[..absoluteStart] + change.Text + previousText[absoluteEnd..];
      }

      public SymbolTable MigrateSymbolTable() {
        var migratedLookupTree = _originalDocument.SymbolTable.LookupTree;
        var migratedDeclarations = _originalDocument.SymbolTable.Locations;
        foreach (var change in _contentChanges) {
          if (change.Range == null) {
            throw new System.InvalidOperationException("the range of the change must not be null");
          }
          var afterChangeEndOffset = GetPositionAtEndOfAppliedChange(change.Range, change.Text);
          migratedLookupTree = ApplyLookupTreeChange(migratedLookupTree, change.Range, afterChangeEndOffset);
          migratedDeclarations = ApplyDeclarationsChange(migratedDeclarations, change.Range, afterChangeEndOffset);
        }
        _logger.LogTrace("migrated the lookup tree, lookup before={SymbolsBefore}, after={SymbolsAfter}",
          _originalDocument.SymbolTable.LookupTree.Count, migratedLookupTree.Count);
        return new SymbolTable(
          _originalDocument.SymbolTable.CompilationUnit,
          _originalDocument.SymbolTable.Declarations,
          migratedDeclarations,
          migratedLookupTree,
          false
        );
      }

      private IIntervalTree<Position, ILocalizableSymbol> ApplyLookupTreeChange(
          IIntervalTree<Position, ILocalizableSymbol> previousLookupTree, Range changeRange, Position afterChangeEndOffset
      ) {
        var migratedLookupTree = new IntervalTree<Position, ILocalizableSymbol>();
        foreach (var entry in previousLookupTree) {
          if (IsPositionBeforeChange(changeRange, entry.To)) {
            migratedLookupTree.Add(entry.From, entry.To, entry.Value);
          }
          if (IsPositionAfterChange(changeRange, entry.From)) {
            var beforeChangeEndOffset = changeRange.End;
            var from = GetPositionWithOffset(entry.From, beforeChangeEndOffset, afterChangeEndOffset);
            var to = GetPositionWithOffset(entry.To, beforeChangeEndOffset, afterChangeEndOffset);
            migratedLookupTree.Add(from, to, entry.Value);
          }
        }
        return migratedLookupTree;
      }

      private Position GetPositionAtEndOfAppliedChange(Range changeRange, string changeText) {
        var changeStart = changeRange.Start;
        var changeEof = changeText.GetEofPosition();
        var characterOffset = changeEof.Character;
        if (changeEof.Line == 0) {
          characterOffset = changeStart.Character + changeEof.Character;
        }
        return new Position(changeStart.Line + changeEof.Line, characterOffset);
      }

      private static Position GetPositionWithOffset(Position position, Position originalOffset, Position changeOffset) {
        int newLine = position.Line - originalOffset.Line + changeOffset.Line;
        int newCharacter = position.Character;
        if (newLine == changeOffset.Line) {
          // The end of the change occured within the line of the given position.
          newCharacter = position.Character - originalOffset.Character + changeOffset.Character - 1;
        }
        return new Position(newLine, newCharacter);
      }

      private static bool IsPositionBeforeChange(Range changeRange, Position symbolTo) {
        return symbolTo.CompareTo(changeRange.Start) <= 0;
      }

      private static bool IsPositionAfterChange(Range changeRange, Position symbolFrom) {
        return symbolFrom.CompareTo(changeRange.End) >= 0;
      }

      private IDictionary<ISymbol, SymbolLocation> ApplyDeclarationsChange(
          IDictionary<ISymbol, SymbolLocation> previousDeclarations, Range changeRange, Position afterChangeEndOffset
      ) {
        var migratedDeclarations = new Dictionary<ISymbol, SymbolLocation>();
        foreach (var (symbol, location) in previousDeclarations) {
          if (!_originalDocument.IsDocument(location.Uri)) {
            migratedDeclarations.Add(symbol, location);
            continue;
          }
          var newLocation = ComputeNewSymbolLocation(location, changeRange, afterChangeEndOffset);
          if (newLocation != null) {
            migratedDeclarations.Add(symbol, newLocation);
          }
        }
        return migratedDeclarations;
      }

      private static SymbolLocation? ComputeNewSymbolLocation(SymbolLocation oldLocation, Range changeRange, Position afterChangeEndOffset) {
        var identifier = ComputeNewRange(oldLocation.Name, changeRange, afterChangeEndOffset);
        if (identifier == null) {
          return null;
        }
        var declaration = ComputeNewRange(oldLocation.Declaration, changeRange, afterChangeEndOffset);
        if (declaration == null) {
          return null;
        }
        return new SymbolLocation(oldLocation.Uri, identifier, declaration);
      }

      private static Range? ComputeNewRange(Range oldRange, Range changeRange, Position afterChangeEndOffset) {
        if (IsPositionBeforeChange(changeRange, oldRange.End)) {
          // The range is strictly before the change.
          return oldRange;
        }
        var beforeChangeEndOffset = changeRange.End;
        if (IsPositionAfterChange(changeRange, oldRange.Start)) {
          // The range is strictly after the change.
          var from = GetPositionWithOffset(oldRange.Start, beforeChangeEndOffset, afterChangeEndOffset);
          var to = GetPositionWithOffset(oldRange.End, beforeChangeEndOffset, afterChangeEndOffset);
          return new Range(from, to);
        }
        if (IsPositionBeforeChange(changeRange, oldRange.Start) && IsPositionAfterChange(changeRange, oldRange.End)) {
          // The change is inbetween the range.
          var to = GetPositionWithOffset(oldRange.End, beforeChangeEndOffset, afterChangeEndOffset);
          return new Range(oldRange.Start, to);
        }
        // The change overlaps with the start and/or the end of the range. We cannot compute a reliable change.
        return null;
      }
    }
  }
}
