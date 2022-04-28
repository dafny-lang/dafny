using IntervalTree;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Util;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Linq;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Workspace.ChangeProcessors {
  public class Relocator : IRelocator {
    private readonly ILogger logger;
    private readonly ILogger<SymbolTable> loggerSymbolTable;

    public Relocator(
      ILogger<Relocator> logger,
      ILogger<SymbolTable> loggerSymbolTable
      ) {
      this.logger = logger;
      this.loggerSymbolTable = loggerSymbolTable;
    }

    public SymbolTable RelocateSymbols(SymbolTable originalSymbolTable, DidChangeTextDocumentParams changes, CancellationToken cancellationToken) {
      return new ChangeProcessor(logger, loggerSymbolTable, changes.ContentChanges, cancellationToken).MigrateSymbolTable(originalSymbolTable);
    }

    public IReadOnlyList<Diagnostic> RelocateDiagnostics(IReadOnlyList<Diagnostic> originalDiagnostics, DidChangeTextDocumentParams changes, CancellationToken cancellationToken) {
      return new ChangeProcessor(logger, loggerSymbolTable, changes.ContentChanges, cancellationToken).MigrateDiagnostics(originalDiagnostics);
    }

    private class ChangeProcessor {
      private readonly ILogger logger;
      private readonly Container<TextDocumentContentChangeEvent> contentChanges;
      private readonly CancellationToken cancellationToken;
      private readonly ILogger<SymbolTable> loggerSymbolTable;

      public ChangeProcessor(
        ILogger logger,
        ILogger<SymbolTable> loggerSymbolTable,
        Container<TextDocumentContentChangeEvent> contentChanges,
        CancellationToken cancellationToken
      ) {
        this.logger = logger;
        this.contentChanges = contentChanges;
        this.cancellationToken = cancellationToken;
        this.loggerSymbolTable = loggerSymbolTable;
      }

      public IReadOnlyList<Diagnostic> MigrateDiagnostics(IReadOnlyList<Diagnostic> originalDiagnostics) {
        return contentChanges.Aggregate(originalDiagnostics, MigrateDiagnostics);
      }

      private IReadOnlyList<Diagnostic> MigrateDiagnostics(IReadOnlyList<Diagnostic> originalDiagnostics, TextDocumentContentChangeEvent change) {
        if (change.Range == null) {
          return new List<Diagnostic>();
        }

        return originalDiagnostics.SelectMany(diagnostic =>
          MigrateDiagnostic(change.Range, change.Text, diagnostic)).ToList();
      }

      private IEnumerable<Diagnostic> MigrateDiagnostic(Range changeRange, string changeText, Diagnostic diagnostic) {
        cancellationToken.ThrowIfCancellationRequested();

        var afterChangeEndOffset = GetPositionAtEndOfAppliedChange(changeRange, changeText);
        var newRange = MigrateRange(diagnostic.Range, changeRange, afterChangeEndOffset);
        if (newRange == null) {
          yield break;
        }

        var newRelatedInformation = diagnostic.RelatedInformation?.SelectMany(related =>
          MigrateRelatedInformation(changeRange, related, afterChangeEndOffset)).ToList();
        yield return diagnostic with { Range = newRange, RelatedInformation = newRelatedInformation };
      }

      private static IEnumerable<DiagnosticRelatedInformation> MigrateRelatedInformation(Range changeRange,
        DiagnosticRelatedInformation related, Position afterChangeEndOffset) {
        var migratedRange = MigrateRange(related.Location.Range, changeRange, afterChangeEndOffset);
        if (migratedRange == null) {
          yield break;
        }

        yield return related with {
          Location = related.Location with {
            Range = migratedRange
          }
        };
      }

      public SymbolTable MigrateSymbolTable(SymbolTable originalSymbolTable) {
        var migratedLookupTree = originalSymbolTable.LookupTree;
        var migratedDeclarations = originalSymbolTable.Locations;
        foreach (var change in contentChanges) {
          cancellationToken.ThrowIfCancellationRequested();
          Position? afterChangeEndOffset = null;
          if (change.Range == null) {
            migratedLookupTree = new IntervalTree<Position, ILocalizableSymbol>();
          } else {
            afterChangeEndOffset = GetPositionAtEndOfAppliedChange(change.Range, change.Text);
            migratedLookupTree = ApplyLookupTreeChange(migratedLookupTree, change.Range, afterChangeEndOffset);
          }
          migratedDeclarations = ApplyDeclarationsChange(originalSymbolTable, migratedDeclarations, change.Range, afterChangeEndOffset);
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
          } else if (IsPositionAfterChange(changeRange, entry.From)) {
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

      private static Range? MigrateRange(Range rangeToMigrate, Range changeRange, Position afterChangeEndOffset) {
        if (!rangeToMigrate.Contains(changeRange) && rangeToMigrate.Intersects(changeRange)) {
          // Do not migrate ranges that partially overlap with the change
          return null;
        }

        var start = MigratePosition(rangeToMigrate.Start, changeRange, afterChangeEndOffset);
        var end = MigratePosition(rangeToMigrate.End, changeRange, afterChangeEndOffset);
        return new Range(start, end);
      }

      private static Position MigratePosition(Position position, Range changeRange, Position afterChangeEndOffset) {
        var changeIsAfterPosition = changeRange.Start >= position && changeRange.End != position;
        if (changeIsAfterPosition) {
          return position;
        }

        return GetPositionWithOffset(position, changeRange.End, afterChangeEndOffset);
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
        SymbolTable originalSymbolTable,
        IDictionary<ISymbol, SymbolLocation> previousDeclarations,
        Range? changeRange,
        Position? afterChangeEndOffset
      ) {
        var migratedDeclarations = new Dictionary<ISymbol, SymbolLocation>();
        foreach (var (symbol, location) in previousDeclarations) {
          cancellationToken.ThrowIfCancellationRequested();
          if (!originalSymbolTable.CompilationUnit.Program.IsEntryDocument(location.Uri)) {
            migratedDeclarations.Add(symbol, location);
            continue;
          }
          if (changeRange == null || afterChangeEndOffset == null) {
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
