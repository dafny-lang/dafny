using IntervalTree;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Util;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Threading;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;

namespace Microsoft.Dafny.LanguageServer.Workspace.ChangeProcessors {
  public class Relocator : IRelocator {
    public const string OutdatedPrefix = "Outdated: ";

    private readonly ILogger logger;
    private readonly ILogger<SignatureAndCompletionTable> loggerSymbolTable;

    public Relocator(
      ILogger<Relocator> logger,
      ILogger<SignatureAndCompletionTable> loggerSymbolTable
      ) {
      this.logger = logger;
      this.loggerSymbolTable = loggerSymbolTable;
    }

    public Position RelocatePosition(Position position, DidChangeTextDocumentParams changes, CancellationToken cancellationToken) {
      return new ChangeProcessor(logger, loggerSymbolTable, changes.ContentChanges, cancellationToken).MigratePosition(position);
    }

    public Range? RelocateRange(Range range, DidChangeTextDocumentParams changes, CancellationToken cancellationToken) {
      return new ChangeProcessor(logger, loggerSymbolTable, changes.ContentChanges, cancellationToken).MigrateRange(range);
    }

    public SignatureAndCompletionTable RelocateSymbols(SignatureAndCompletionTable originalSymbolTable, DidChangeTextDocumentParams changes, CancellationToken cancellationToken) {
      return new ChangeProcessor(logger, loggerSymbolTable, changes.ContentChanges, cancellationToken).MigrateSymbolTable(originalSymbolTable);
    }

    public IReadOnlyList<Diagnostic> RelocateDiagnostics(IReadOnlyList<Diagnostic> originalDiagnostics, DidChangeTextDocumentParams changes, CancellationToken cancellationToken) {
      return new ChangeProcessor(logger, loggerSymbolTable, changes.ContentChanges, cancellationToken).MigrateDiagnostics(originalDiagnostics);
    }

    public VerificationTree RelocateVerificationTree(VerificationTree originalVerificationTree,
      int lines,
      DidChangeTextDocumentParams changes, CancellationToken cancellationToken) {
      var changeProcessor = new ChangeProcessor(logger, loggerSymbolTable, changes.ContentChanges, cancellationToken);
      var migratedChildren = changeProcessor.MigrateVerificationTrees(originalVerificationTree.Children);
      return originalVerificationTree with {
        Children = migratedChildren.ToList(),
        Range = DocumentVerificationTree.LinesToRange(lines),
        StatusCurrent = CurrentStatus.Obsolete
      };
    }

    public ImmutableList<Position> RelocatePositions(ImmutableList<Position> originalPositions,
      DidChangeTextDocumentParams changes, CancellationToken cancellationToken) {
      var migratePositions = new ChangeProcessor(logger, loggerSymbolTable, changes.ContentChanges, cancellationToken)
        .MigratePositions(originalPositions);
      return migratePositions;
    }

    private class ChangeProcessor {

      private readonly ILogger logger;
      // Invariant: Item1.Range == null <==> Item2 == null 
      private readonly List<TextDocumentContentChangeEvent> contentChanges;
      private readonly CancellationToken cancellationToken;
      private readonly ILogger<SignatureAndCompletionTable> loggerSymbolTable;

      public ChangeProcessor(
        ILogger logger,
        ILogger<SignatureAndCompletionTable> loggerSymbolTable,
        Container<TextDocumentContentChangeEvent> contentChanges,
        CancellationToken cancellationToken
      ) {
        this.logger = logger;
        this.contentChanges = contentChanges.ToList();
        this.cancellationToken = cancellationToken;
        this.loggerSymbolTable = loggerSymbolTable;
      }

      public Position MigratePosition(Position position) {
        return contentChanges.Aggregate(position, (partiallyMigratedPosition, change) => {
          if (change.Range == null) {
            return partiallyMigratedPosition;
          }

          return MigratePosition(position, change);
        });
      }

      public Range? MigrateRange(Range range) {
        return contentChanges.Aggregate<TextDocumentContentChangeEvent, Range?>(range,
          (intermediateRange, change) => intermediateRange == null ? null : MigrateRange(intermediateRange, change));
      }

      public IReadOnlyList<Diagnostic> MigrateDiagnostics(IReadOnlyList<Diagnostic> originalDiagnostics) {
        return contentChanges.Aggregate(originalDiagnostics, MigrateDiagnostics);
      }

      public ImmutableList<Position> MigratePositions(ImmutableList<Position> originalRanges) {
        return contentChanges.Aggregate(originalRanges, MigratePositions);
      }

      private IReadOnlyList<Diagnostic> MigrateDiagnostics(IReadOnlyList<Diagnostic> originalDiagnostics, TextDocumentContentChangeEvent change) {
        if (change.Range == null) {
          return new List<Diagnostic>();
        }

        return originalDiagnostics.SelectMany(diagnostic => MigrateDiagnostic(change, diagnostic)).ToList();
      }
      private ImmutableList<Position> MigratePositions(ImmutableList<Position> originalRanges, TextDocumentContentChangeEvent change) {
        if (change.Range == null) {
          return new List<Position> { }.ToImmutableList();
        }

        return originalRanges.SelectMany(position => MigratePosition(change, position)).ToImmutableList();
      }

      // Requires changeEndOffset.change.Range to be not null
      private IEnumerable<Position> MigratePosition(TextDocumentContentChangeEvent change, Position position) {
        if (change.Range!.Contains(position)) {
          return Enumerable.Empty<Position>();
        }

        return new List<Position> { MigratePosition(position, change) };
      }

      // TODO change the signature.
      private IEnumerable<Diagnostic> MigrateDiagnostic(TextDocumentContentChangeEvent change, Diagnostic diagnostic) {
        cancellationToken.ThrowIfCancellationRequested();

        var newRange = MigrateRange(diagnostic.Range, change);
        if (newRange == null) {
          yield break;
        }

        var newRelatedInformation = diagnostic.RelatedInformation?.SelectMany(related =>
          MigrateRelatedInformation(change, related)).ToList();
        yield return diagnostic with {
          Message = diagnostic.Message.StartsWith(OutdatedPrefix) ? diagnostic.Message : OutdatedPrefix + diagnostic.Message,
          Severity = diagnostic.Severity == DiagnosticSeverity.Error ? DiagnosticSeverity.Warning : diagnostic.Severity,
          Range = newRange,
          RelatedInformation = newRelatedInformation
        };
      }

      private IEnumerable<DiagnosticRelatedInformation> MigrateRelatedInformation(TextDocumentContentChangeEvent change,
        DiagnosticRelatedInformation related) {
        var migratedRange = MigrateRange(related.Location.Range, change);
        if (migratedRange == null) {
          yield break;
        }

        yield return related with {
          Location = related.Location with {
            Range = migratedRange
          }
        };
      }

      public SignatureAndCompletionTable MigrateSymbolTable(SignatureAndCompletionTable originalSymbolTable) {
        var migratedLookupTree = originalSymbolTable.LookupTree;
        var migratedDeclarations = originalSymbolTable.Locations;
        foreach (var change in contentChanges) {
          cancellationToken.ThrowIfCancellationRequested();
          if (change.Range == null) {
            migratedLookupTree = new IntervalTree<Position, ILocalizableSymbol>();
          } else {
            migratedLookupTree = ApplyLookupTreeChange(migratedLookupTree, change);
          }
          migratedDeclarations = ApplyDeclarationsChange(originalSymbolTable, migratedDeclarations, change.Range, GetPositionAtEndOfAppliedChange(change));
        }
        logger.LogTrace("migrated the lookup tree, lookup before={SymbolsBefore}, after={SymbolsAfter}",
          originalSymbolTable.LookupTree.Count, migratedLookupTree.Count);
        return new SignatureAndCompletionTable(
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
        TextDocumentContentChangeEvent change
      ) {
        var migratedLookupTree = new IntervalTree<Position, ILocalizableSymbol>();
        foreach (var entry in previousLookupTree) {
          cancellationToken.ThrowIfCancellationRequested();
          if (IsPositionBeforeChange(change.Range!, entry.To)) {
            migratedLookupTree.Add(entry.From, entry.To, entry.Value);
          } else if (IsPositionAfterChange(change.Range!, entry.From)) {
            var beforeChangeEndOffset = change.Range!.End;
            var afterChangeEndOffset = GetPositionAtEndOfAppliedChange(change);
            var from = GetPositionWithOffset(entry.From, beforeChangeEndOffset, afterChangeEndOffset!);
            var to = GetPositionWithOffset(entry.To, beforeChangeEndOffset, afterChangeEndOffset!);
            migratedLookupTree.Add(from, to, entry.Value);
          }
        }
        return migratedLookupTree;
      }

      private readonly Dictionary<TextDocumentContentChangeEvent, Position> getPositionAtEndOfAppliedChangeCache = new();
      private Position? GetPositionAtEndOfAppliedChange(TextDocumentContentChangeEvent change) {
        if (change.Range == null) {
          return null;
        }
        return getPositionAtEndOfAppliedChangeCache.GetOrCreate(change, Compute);

        Position Compute() {
          var changeStart = change.Range!.Start;
          var changeEof = GetEofPosition(change.Text);
          var characterOffset = changeEof.Character;
          if (changeEof.Line == 0) {
            characterOffset = changeStart.Character + changeEof.Character;
          }

          return new Position(changeStart.Line + changeEof.Line, characterOffset);
        }
      }

      /// <summary>
      /// Gets the LSP position at the end of the given text.
      /// </summary>
      /// <param name="text">The text to get the LSP end of.</param>
      /// <param name="cancellationToken">A token to cancel the resolution before its completion.</param>
      /// <returns>The LSP position at the end of the text.</returns>
      /// <exception cref="ArgumentException">Thrown if the specified position does not belong to the given text.</exception>
      /// <exception cref="OperationCanceledException">Thrown when the cancellation was requested before completion.</exception>
      /// <exception cref="ObjectDisposedException">Thrown if the cancellation token was disposed before the completion.</exception>
      private static Position GetEofPosition(string text, CancellationToken cancellationToken = default) {
        int line = 0;
        int character = 0;
        int absolutePosition = 0;
        do {
          cancellationToken.ThrowIfCancellationRequested();
          if (IsEndOfLine(text, absolutePosition)) {
            line++;
            character = 0;
          } else {
            character++;
          }
          absolutePosition++;
        } while (absolutePosition <= text.Length);
        return new Position(line, character);
      }

      private static bool IsEndOfLine(string text, int absolutePosition) {
        if (absolutePosition >= text.Length) {
          return false;
        }
        return text[absolutePosition] switch {
          '\n' => true,
          '\r' => absolutePosition + 1 == text.Length || text[absolutePosition + 1] != '\n',
          _ => false
        };
      }

      public Range? MigrateRange(Range rangeToMigrate, TextDocumentContentChangeEvent change) {
        if (!rangeToMigrate.Contains(change.Range!) && rangeToMigrate.Intersects(change.Range!)) {
          // Do not migrate ranges that partially overlap with the change
          return null;
        }

        var start = MigratePosition(rangeToMigrate.Start, change);
        var end = MigratePosition(rangeToMigrate.End, change);
        return new Range(start, end);
      }

      private Position MigratePosition(Position position, TextDocumentContentChangeEvent change) {
        var changeIsAfterPosition = change.Range!.Start >= position && change.Range!.End != position;
        if (changeIsAfterPosition) {
          return position;
        }

        return GetPositionWithOffset(position, change.Range!.End, GetPositionAtEndOfAppliedChange(change)!);
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
        SignatureAndCompletionTable originalSymbolTable,
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

      public IEnumerable<VerificationTree> MigrateVerificationTrees(IEnumerable<VerificationTree> originalDiagnostics) {
        return contentChanges.Aggregate(originalDiagnostics, MigrateVerificationTrees);
      }
      private IEnumerable<VerificationTree> MigrateVerificationTrees(IEnumerable<VerificationTree> verificationTrees, TextDocumentContentChangeEvent change) {
        if (change.Range == null) {
          yield break;
        }

        foreach (var verificationTree in verificationTrees) {
          var newRange = MigrateRange(verificationTree.Range, change);
          if (newRange == null) {
            continue;
          }
          var newNodeDiagnostic = verificationTree with {
            Range = newRange,
            Children = MigrateVerificationTrees(verificationTree.Children, change).ToList(),
            StatusVerification = verificationTree.StatusVerification,
            StatusCurrent = CurrentStatus.Obsolete,
            Finished = false,
            Started = false
          };
          if (newNodeDiagnostic is AssertionVerificationTree assertionNodeDiagnostic) {
            newNodeDiagnostic = assertionNodeDiagnostic with {
              SecondaryPosition = assertionNodeDiagnostic.SecondaryPosition != null
                ? MigratePosition(assertionNodeDiagnostic.SecondaryPosition, change)
                : null
            };
          }
          yield return newNodeDiagnostic;
        }
      }
    }
  }
}
