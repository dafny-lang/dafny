using IntervalTree;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Util;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Workspace.ChangeProcessors {
  public class SymbolTableRelocator : ISymbolTableRelocator {
    private readonly ILogger logger;
    private readonly ILogger<SymbolTable> loggerSymbolTable;

    public SymbolTableRelocator(
      ILogger<SymbolTableRelocator> logger,
      ILogger<SymbolTable> loggerSymbolTable
      ) {
      this.logger = logger;
      this.loggerSymbolTable = loggerSymbolTable;
    }

    public SymbolTable Relocate(SymbolTable originalSymbolTable, DidChangeTextDocumentParams changes, CancellationToken cancellationToken) {
      return new ChangeProcessor(logger, loggerSymbolTable, originalSymbolTable, changes.ContentChanges, cancellationToken).MigrateSymbolTable();
    }

    private class ChangeProcessor {
      private readonly ILogger logger;
      private readonly SymbolTable originalSymbolTable;
      private readonly Container<TextDocumentContentChangeEvent> contentChanges;
      private readonly CancellationToken cancellationToken;
      private readonly ILogger<SymbolTable> loggerSymbolTable;

      public ChangeProcessor(
        ILogger logger,
        ILogger<SymbolTable> loggerSymbolTable,
        SymbolTable originalSymbolTable,
        Container<TextDocumentContentChangeEvent> contentChanges,
        CancellationToken cancellationToken
      ) {
        this.logger = logger;
        this.originalSymbolTable = originalSymbolTable;
        this.contentChanges = contentChanges;
        this.cancellationToken = cancellationToken;
        this.loggerSymbolTable = loggerSymbolTable;
      }

      public SymbolTable MigrateSymbolTable() {
        var migratedLookupTree = originalSymbolTable.LookupTree;
        var migratedDeclarations = originalSymbolTable.Locations;
        foreach (var change in contentChanges) {
          cancellationToken.ThrowIfCancellationRequested();
          if (change.Range == null) {
            throw new System.InvalidOperationException("the range of the change must not be null");
          }
          var afterChangeEndOffset = GetPositionAtEndOfAppliedChange(change.Range, change.Text);
          migratedLookupTree = ApplyLookupTreeChange(migratedLookupTree, change.Range, afterChangeEndOffset);
          migratedDeclarations = ApplyDeclarationsChange(migratedDeclarations, change.Range, afterChangeEndOffset);
        }
        logger.LogTrace("migrated the lookup tree, lookup before={SymbolsBefore}, after={SymbolsAfter}",
          originalSymbolTable.LookupTree.Count, migratedLookupTree.Count);
        return new SymbolTable(
          loggerSymbolTable,
          originalSymbolTable.CompilationUnit,
          originalSymbolTable.Declarations,
          migratedDeclarations,
          migratedLookupTree,
          false
        );
      }

      private IIntervalTree<Position, ILocalizableSymbol> ApplyLookupTreeChange(
        IIntervalTree<Position, ILocalizableSymbol> previousLookupTree,
        Range changeRange,
        Position afterChangeEndOffset
      ) {
        var migratedLookupTree = new IntervalTree<Position, ILocalizableSymbol>();
        foreach (var entry in previousLookupTree) {
          cancellationToken.ThrowIfCancellationRequested();
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
        IDictionary<ISymbol, SymbolLocation> previousDeclarations,
        Range changeRange,
        Position afterChangeEndOffset
      ) {
        var migratedDeclarations = new Dictionary<ISymbol, SymbolLocation>();
        foreach (var (symbol, location) in previousDeclarations) {
          cancellationToken.ThrowIfCancellationRequested();
          if (!originalSymbolTable.CompilationUnit.Program.IsEntryDocument(location.Uri)) {
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
