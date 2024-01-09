using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace.ChangeProcessors;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public record IdeImplementationView(Range Range, PublishedVerificationStatus Status,
  IReadOnlyList<Diagnostic> Diagnostics, bool HitErrorLimit);

public enum VerificationPreparationState { NotStarted, InProgress, Done }
public record IdeVerificationResult(VerificationPreparationState PreparationProgress, ImmutableDictionary<string, IdeImplementationView> Implementations);

/// <summary>
/// Contains information from the latest document, and from older documents if some information is missing,
/// to provide the IDE with as much information as possible.
/// </summary>
public record IdeState(
  int Version,
  ISet<Uri> OwnedUris,
  CompilationInput Input,
  CompilationStatus Status,
  Node Program,
  ImmutableDictionary<Uri, ImmutableList<Diagnostic>> StaticDiagnostics,
  Node? ResolvedProgram,
  SymbolTable SymbolTable,
  LegacySignatureAndCompletionTable SignatureAndCompletionTable,
  ImmutableDictionary<Uri, ImmutableDictionary<Range, IdeVerificationResult>> VerificationResults,
  IReadOnlyList<Counterexample> Counterexamples,
  IReadOnlyDictionary<Uri, IReadOnlyList<Range>> GhostRanges,
  ImmutableDictionary<Uri, DocumentVerificationTree> VerificationTrees
) {
  public Uri Uri => Input.Uri.ToUri();

  public static IEnumerable<Diagnostic> MarkDiagnosticsAsOutdated(IEnumerable<Diagnostic> diagnostics) {
    return diagnostics.Select(diagnostic => diagnostic with {
      Severity = diagnostic.Severity == DiagnosticSeverity.Error ? DiagnosticSeverity.Warning : diagnostic.Severity,
      Message = diagnostic.Message.StartsWith(OutdatedPrefix)
        ? diagnostic.Message
        : OutdatedPrefix + diagnostic.Message
    });
  }

  public const string OutdatedPrefix = "Outdated: ";

  public IdeState Migrate(DafnyOptions options, Migrator migrator, int newVersion, bool clientSide) {
    var migratedVerificationTrees = VerificationTrees.ToImmutableDictionary(
      kv => kv.Key, kv =>
        (DocumentVerificationTree)migrator.RelocateVerificationTree(kv.Value));

    var verificationResults = clientSide
      ? VerificationResults
      : MigrateImplementationViews(migrator, VerificationResults);
    return this with {
      Version = newVersion,
      Status = CompilationStatus.Parsing,
      VerificationResults = verificationResults,
      SignatureAndCompletionTable = options.Get(LegacySignatureAndCompletionTable.MigrateSignatureAndCompletionTable)
        ? migrator.MigrateSymbolTable(SignatureAndCompletionTable) : LegacySignatureAndCompletionTable.Empty(options, Input.Project),
      VerificationTrees = migratedVerificationTrees
    };
  }

  private ImmutableDictionary<Uri, ImmutableDictionary<Range, IdeVerificationResult>> MigrateImplementationViews(
    Migrator migrator,
    ImmutableDictionary<Uri, ImmutableDictionary<Range, IdeVerificationResult>> oldVerificationDiagnostics) {
    var uri = migrator.MigratedUri;
    var previous = oldVerificationDiagnostics.GetValueOrDefault(uri);
    if (previous == null) {
      return oldVerificationDiagnostics;
    }
    var result = ImmutableDictionary<Range, IdeVerificationResult>.Empty;
    foreach (var entry in previous) {
      var newOuterRange = migrator.MigrateRange(entry.Key);
      if (newOuterRange == null) {
        continue;
      }

      var newValue = ImmutableDictionary<string, IdeImplementationView>.Empty;
      foreach (var innerEntry in entry.Value.Implementations) {
        var newInnerRange = migrator.MigrateRange(innerEntry.Value.Range);
        if (newInnerRange != null) {
          newValue = newValue.Add(innerEntry.Key, innerEntry.Value with {
            Range = newInnerRange,
            Diagnostics = migrator.MigrateDiagnostics(innerEntry.Value.Diagnostics)
          });
        }
      }

      result = result.Add(newOuterRange, entry.Value with { Implementations = newValue });
    }

    return oldVerificationDiagnostics.SetItem(uri, result);
  }

  public IReadOnlyDictionary<Range, IdeVerificationResult> GetVerificationResults(Uri uri) {
    return VerificationResults.GetValueOrDefault(uri) ??
      ((IReadOnlyDictionary<Range, IdeVerificationResult>)ImmutableDictionary<Range, IdeVerificationResult>.Empty);
  }

  public IEnumerable<Diagnostic> GetAllDiagnostics() {
    return GetDiagnosticUris().SelectMany(GetDiagnosticsForUri);
  }

  public IEnumerable<Diagnostic> GetDiagnosticsForUri(Uri uri) {
    var resolutionDiagnostics = StaticDiagnostics.GetValueOrDefault(uri) ?? Enumerable.Empty<Diagnostic>();
    var verificationDiagnostics = GetVerificationResults(uri).SelectMany(x => {
      return x.Value.Implementations.Values.SelectMany(v => v.Diagnostics).Concat(GetErrorLimitDiagnostics(x));
    });
    return resolutionDiagnostics.Concat(verificationDiagnostics);
  }

  private static IEnumerable<Diagnostic> GetErrorLimitDiagnostics(KeyValuePair<Range, IdeVerificationResult> x) {
    var anyImplementationHitErrorLimit = x.Value.Implementations.Values.Any(i => i.HitErrorLimit);
    IEnumerable<Diagnostic> result;
    if (anyImplementationHitErrorLimit) {
      var diagnostic = new Diagnostic() {
        Severity = DiagnosticSeverity.Warning,
        Code = new DiagnosticCode("errorLimitHit"),
        Message =
          "Verification hit error limit so not all errors may be shown. Configure this limit using --error-limit",
        Range = x.Key,
        Source = MessageSource.Verifier.ToString()
      };
      result = new[] { diagnostic };
    } else {
      result = Enumerable.Empty<Diagnostic>();
    }

    return result;
  }

  public IEnumerable<Uri> GetDiagnosticUris() {
    return StaticDiagnostics.Keys.Concat(VerificationResults.Keys);
  }
}

public static class Util {
  public static Diagnostic ToLspDiagnostic(this DafnyDiagnostic dafnyDiagnostic) {
    return new Diagnostic {
      Code = dafnyDiagnostic.ErrorId,
      Severity = ToSeverity(dafnyDiagnostic.Level),
      Message = dafnyDiagnostic.Message,
      Range = dafnyDiagnostic.Token.GetLspRange(),
      Source = dafnyDiagnostic.Source.ToString(),
      RelatedInformation = dafnyDiagnostic.RelatedInformation.Select(r =>
        new DiagnosticRelatedInformation {
          Location = CreateLocation(r.Token),
          Message = r.Message
        }).ToList(),
      CodeDescription = dafnyDiagnostic.ErrorId == null
        ? null
        : new CodeDescription { Href = new Uri("https://dafny.org/dafny/HowToFAQ/Errors#" + dafnyDiagnostic.ErrorId) },
    };
  }

  public static Location CreateLocation(IToken token) {
    var uri = DocumentUri.Parse(token.Uri.AbsoluteUri);
    return new Location {
      Range = token.GetLspRange(),
      // During parsing, we store absolute paths to make reconstructing the Uri easier
      // https://github.com/dafny-lang/dafny/blob/06b498ee73c74660c61042bb752207df13930376/Source/DafnyLanguageServer/Language/DafnyLangParser.cs#L59 
      Uri = uri
    };
  }

  private static DiagnosticSeverity ToSeverity(ErrorLevel level) {
    return level switch {
      ErrorLevel.Error => DiagnosticSeverity.Error,
      ErrorLevel.Warning => DiagnosticSeverity.Warning,
      ErrorLevel.Info => DiagnosticSeverity.Hint,
      _ => throw new ArgumentException($"unknown error level {level}", nameof(level))
    };
  }
}
