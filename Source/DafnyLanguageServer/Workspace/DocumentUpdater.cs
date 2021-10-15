using IntervalTree;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Util;
using Microsoft.Dafny.LanguageServer.Workspace.ChangeProcessors;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Options;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  public class DocumentUpdater : IDocumentUpdater {
    private readonly ILogger logger;
    private readonly DocumentOptions options;
    private readonly ITextChangeProcessor textChangeProcessor;
    private readonly ITextDocumentLoader documentLoader;

    private bool Verify => options.Verify == AutoVerification.OnChange;

    public DocumentUpdater(
      ILogger<DocumentUpdater> logger,
      IOptions<DocumentOptions> options,
      ITextChangeProcessor textChangeProcessor,
      ITextDocumentLoader documentLoader
    ) {
      this.logger = logger;
      this.textChangeProcessor = textChangeProcessor;
      this.options = options.Value;
      this.documentLoader = documentLoader;
    }

    public async Task<DafnyDocument> ApplyChangesAsync(DafnyDocument oldDocument, DidChangeTextDocumentParams documentChange, CancellationToken cancellationToken) {
      // We do not pass the cancellation token to the text change processor because the text has to be kept in sync with the LSP client.
      var updatedText = textChangeProcessor.ApplyChange(oldDocument.Text, documentChange, CancellationToken.None);
      var changeProcessor = new ChangeProcessor(logger, oldDocument, documentChange.ContentChanges);
      try {
        var newDocument = await documentLoader.LoadAsync(updatedText, Verify, cancellationToken);
        if (newDocument.SymbolTable.Resolved) {
          return newDocument;
        }
        // The document loader failed to create a new symbol table. Since we'd still like to provide
        // features such as code completion and lookup, we re-locate the previously resolved symbols
        // according to the change.
        return MigrateDocument(updatedText, newDocument, changeProcessor, false);
      } catch (System.OperationCanceledException) {
        // The document load was canceled before it could complete. We migrate the document
        // to re-locate symbols that were resolved previously.
        logger.LogTrace("document loading canceled, applying migration");
        return MigrateDocument(updatedText, oldDocument, changeProcessor, true);
      }
    }

    private static DafnyDocument MigrateDocument(TextDocumentItem mergedText, DafnyDocument document, ChangeProcessor changeProcessor, bool loadCanceled) {
      return new DafnyDocument(
        mergedText,
        document.Errors,
        document.Program,
        changeProcessor.MigrateSymbolTable(),
        serializedCounterExamples: null,
        loadCanceled
      );
    }

    private class ChangeProcessor {
      private readonly ILogger logger;
      private readonly DafnyDocument originalDocument;
      private readonly Container<TextDocumentContentChangeEvent> contentChanges;

      public ChangeProcessor(ILogger logger, DafnyDocument originalDocument, Container<TextDocumentContentChangeEvent> contentChanges) {
        this.logger = logger;
        this.originalDocument = originalDocument;
        this.contentChanges = contentChanges;
      }

      public SymbolTable MigrateSymbolTable() {
        var migratedLookupTree = originalDocument.SymbolTable.LookupTree;
        var migratedDeclarations = originalDocument.SymbolTable.Locations;
        foreach (var change in contentChanges) {
          if (change.Range == null) {
            throw new System.InvalidOperationException("the range of the change must not be null");
          }
          var afterChangeEndOffset = GetPositionAtEndOfAppliedChange(change.Range, change.Text);
          migratedLookupTree = ApplyLookupTreeChange(migratedLookupTree, change.Range, afterChangeEndOffset);
          migratedDeclarations = ApplyDeclarationsChange(migratedDeclarations, change.Range, afterChangeEndOffset);
        }
        logger.LogTrace("migrated the lookup tree, lookup before={SymbolsBefore}, after={SymbolsAfter}",
          originalDocument.SymbolTable.LookupTree.Count, migratedLookupTree.Count);
        return new SymbolTable(
          originalDocument.SymbolTable.CompilationUnit,
          originalDocument.SymbolTable.Declarations,
          migratedDeclarations,
          migratedLookupTree,
          false
        );
      }

      private static IIntervalTree<Position, ILocalizableSymbol> ApplyLookupTreeChange(
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

      private static Position GetPositionAtEndOfAppliedChange(Range changeRange, string changeText) {
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
          if (!originalDocument.IsDocument(location.Uri)) {
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
