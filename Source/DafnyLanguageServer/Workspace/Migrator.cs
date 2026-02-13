using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading;
using IntervalTree;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Workspace.ChangeProcessors;

public delegate Migrator CreateMigrator(DidChangeTextDocumentParams changeParams, CancellationToken cancellationToken);

public interface IMigrator {
  VerificationTree RelocateVerificationTree(VerificationTree tree);
  Uri MigratedUri { get; }
  Range? MigrateRange(Range range, bool isFullRange = false);
  IReadOnlyList<Diagnostic> MigrateDiagnostics(IReadOnlyList<Diagnostic> diagnostics);
  LegacySignatureAndCompletionTable MigrateSymbolTable(LegacySignatureAndCompletionTable table);
}

class NoopMigrator : IMigrator {
  public NoopMigrator(Uri migratedUri) {
    MigratedUri = migratedUri;
  }

  public VerificationTree RelocateVerificationTree(VerificationTree tree) {
    return tree;
  }

  public Uri MigratedUri { get; }
  public Range MigrateRange(Range range, bool isFullRange = false) {
    return range;
  }

  public IReadOnlyList<Diagnostic> MigrateDiagnostics(IReadOnlyList<Diagnostic> diagnostics) {
    return diagnostics;
  }

  public LegacySignatureAndCompletionTable MigrateSymbolTable(LegacySignatureAndCompletionTable table) {
    return table;
  }
}


public class Migrator : IMigrator {
  private readonly ILogger<Migrator> logger;
  private readonly DidChangeTextDocumentParams changeParams;
  private readonly CancellationToken cancellationToken;
  private readonly ILogger<LegacySignatureAndCompletionTable> loggerSymbolTable;

  private readonly Dictionary<TextDocumentContentChangeEvent, Position> getPositionAtEndOfAppliedChangeCache = new();

  public Uri MigratedUri => changeParams.TextDocument.Uri.ToUri();

  public Migrator(
    ILogger<Migrator> logger,
    ILogger<LegacySignatureAndCompletionTable> loggerSymbolTable,
    DidChangeTextDocumentParams changeParams,
    CancellationToken cancellationToken
  ) {
    this.logger = logger;
    this.changeParams = changeParams;
    this.cancellationToken = cancellationToken;
    this.loggerSymbolTable = loggerSymbolTable;
  }

  public Position MigratePosition(Position position) {
    return changeParams.ContentChanges.Aggregate(position, (partiallyMigratedPosition, change) => {
      if (change.Range == null) {
        return partiallyMigratedPosition;
      }

      return MigratePosition(position, change);
    });
  }

  public Range? MigrateRange(Range range, bool isFullRange = false) {
    return changeParams.ContentChanges.Aggregate<TextDocumentContentChangeEvent, Range?>(range,
      (intermediateRange, change) => intermediateRange == null ? null : MigrateRange(intermediateRange, change, isFullRange));
  }

  public IReadOnlyList<Diagnostic> MigrateDiagnostics(IReadOnlyList<Diagnostic> originalDiagnostics) {
    return changeParams.ContentChanges.Aggregate(originalDiagnostics, MigrateDiagnostics);
  }

  public ImmutableList<Position> MigratePositions(ImmutableList<Position> originalRanges) {
    return changeParams.ContentChanges.Aggregate(originalRanges, MigratePositions);
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
      return [];
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

  public LegacySignatureAndCompletionTable MigrateSymbolTable(LegacySignatureAndCompletionTable originalSymbolTable) {
    var uri = changeParams.TextDocument.Uri.ToUri();
    var migratedLookupTreeForUri = originalSymbolTable.LookupTreePerUri.GetValueOrDefault(uri);
    var migratedLocationsForUri = originalSymbolTable.LocationsPerUri.GetValueOrDefault(uri);
    foreach (var change in changeParams.ContentChanges) {
      cancellationToken.ThrowIfCancellationRequested();
      if (change.Range == null) {
        migratedLookupTreeForUri = new IntervalTree<Position, ILocalizableSymbol>();
      } else {
        if (migratedLookupTreeForUri != null) {
          migratedLookupTreeForUri = ApplyLookupTreeChange(migratedLookupTreeForUri, change);
        }
      }

      if (migratedLocationsForUri != null) {
        migratedLocationsForUri = ApplyDeclarationsChange(originalSymbolTable, migratedLocationsForUri, change, GetPositionAtEndOfAppliedChange(change));
      }
    }
    if (migratedLookupTreeForUri != null) {
      logger.LogTrace("migrated the lookup tree, lookup before={SymbolsBefore}, after={SymbolsAfter}",
        originalSymbolTable.LookupTreePerUri.Count, migratedLookupTreeForUri.Count);
      // TODO IntervalTree goes out of sync after any change and "fixes" its state upon the first query. Replace it with another implementation that can be queried without potential side-effects.
      migratedLookupTreeForUri.Query(new Position(0, 0));
    }

    var migratedLocations = originalSymbolTable.LocationsPerUri;
    if (migratedLocationsForUri != null) {
      migratedLocations = migratedLocations.SetItem(uri, migratedLocationsForUri);
    }
    var migratedLookupTrees = originalSymbolTable.LookupTreePerUri;
    if (migratedLookupTreeForUri != null) {
      migratedLookupTrees = migratedLookupTrees.SetItem(uri, migratedLookupTreeForUri);
    }
    return new LegacySignatureAndCompletionTable(
      loggerSymbolTable,
      originalSymbolTable.CompilationUnit,
      originalSymbolTable.Declarations,
      migratedLocations,
      migratedLookupTrees,
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
  /// <exception cref="System.ArgumentException">Thrown if the specified position does not belong to the given text.</exception>
  /// <exception cref="System.OperationCanceledException">Thrown when the cancellation was requested before completion.</exception>
  /// <exception cref="System.ObjectDisposedException">Thrown if the cancellation token was disposed before the completion.</exception>
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

  public Range? MigrateRange(Range rangeToMigrate, TextDocumentContentChangeEvent change, bool isFullRange = false) {
    if (change.Range == null || (!rangeToMigrate.Contains(change.Range!) && rangeToMigrate.Intersects(change.Range!))) {
      // Do not migrate ranges that partially overlap with the change
      if (change.Range == null && isFullRange) {
        var newLineRegex = new Regex("\n(?<LastColumn>.*)");
        var matches = newLineRegex.Matches(change.Text);
        var line = matches.Count;
        var col = matches.Count == 0 ? change.Text.Length : matches[^1].Groups["LastColumn"].Value.Length;

        var endPosition = (line, col);
        return new Range((0, 0), endPosition);
      }
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

  private IDictionary<ILegacySymbol, SymbolLocation> ApplyDeclarationsChange(
    LegacySignatureAndCompletionTable originalSymbolTable,
    IDictionary<ILegacySymbol, SymbolLocation> previousDeclarations,
    TextDocumentContentChangeEvent changeRange,
    Position? afterChangeEndOffset
  ) {
    var migratedDeclarations = new Dictionary<ILegacySymbol, SymbolLocation>();
    foreach (var (symbol, location) in previousDeclarations) {
      cancellationToken.ThrowIfCancellationRequested();
      if (location.Uri != changeParams.TextDocument.Uri) {
        migratedDeclarations.Add(symbol, location);
        continue;
      }
      if (changeRange.Range == null || afterChangeEndOffset == null) {
        continue;
      }
      var newLocation = ComputeNewSymbolLocation(location, changeRange.Range, afterChangeEndOffset);
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

  public VerificationTree RelocateVerificationTree(VerificationTree originalVerificationTree) {
    var migratedChildren = MigrateVerificationTrees(originalVerificationTree.Children);
    var migratedRange = MigrateRange(originalVerificationTree.Range, true);
    return originalVerificationTree with {
      Children = new ConcurrentBag<VerificationTree>(migratedChildren),
      Range = migratedRange!,
      StatusCurrent = CurrentStatus.Obsolete
    };
  }

  public IEnumerable<VerificationTree> MigrateVerificationTrees(IEnumerable<VerificationTree> previousTrees) {
    return changeParams.ContentChanges.Aggregate(previousTrees, MigrateVerificationTrees);
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
        Children = new ConcurrentBag<VerificationTree>(MigrateVerificationTrees(verificationTree.Children, change)),
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