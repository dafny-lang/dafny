using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace.ChangeProcessors;

public delegate Migrator CreateMigrator(DidChangeTextDocumentParams changeParams, CancellationToken cancellationToken);

public class Migrator {

  private readonly ILogger<Migrator> logger;
  private readonly DidChangeTextDocumentParams changeParams;
  private readonly CancellationToken cancellationToken;

  private readonly Dictionary<TextDocumentContentChangeEvent, Position> getPositionAtEndOfAppliedChangeCache = new();

  public Migrator(
    ILogger<Migrator> logger,
    DidChangeTextDocumentParams changeParams,
    CancellationToken cancellationToken
  ) {
    this.logger = logger;
    this.changeParams = changeParams;
    this.cancellationToken = cancellationToken;
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

  public VerificationTree RelocateVerificationTree(VerificationTree originalVerificationTree) {
    var migratedChildren = MigrateVerificationTrees(originalVerificationTree.Children);
    var migratedRange = MigrateRange(originalVerificationTree.Range, true);
    return originalVerificationTree with {
      Children = migratedChildren.ToList(),
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