using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Reactive;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public class CompilationAfterResolution : CompilationAfterParsing {

  public CompilationAfterResolution(CompilationAfterParsing compilationAfterParsing,
    IReadOnlyDictionary<Uri, List<DafnyDiagnostic>> diagnostics,
    SymbolTable? symbolTable,
    LegacySignatureAndCompletionTable signatureAndCompletionTable,
    IReadOnlyDictionary<Uri, IReadOnlyList<Range>> ghostDiagnostics,
    IReadOnlyList<ICanVerify>? verifiables,
    LazyConcurrentDictionary<ModuleDefinition, Task<IReadOnlyDictionary<FilePosition, IReadOnlyList<IImplementationTask>>>> translatedModules,
    List<Counterexample> counterexamples
    ) :
    base(compilationAfterParsing, compilationAfterParsing.Program, diagnostics, compilationAfterParsing.VerificationTrees) {
    SymbolTable = symbolTable;
    SignatureAndCompletionTable = signatureAndCompletionTable;
    GhostDiagnostics = ghostDiagnostics;
    Verifiables = verifiables;
    TranslatedModules = translatedModules;
    Counterexamples = counterexamples;
  }
  public List<Counterexample> Counterexamples { get; set; }
  public SymbolTable? SymbolTable { get; }
  public LegacySignatureAndCompletionTable SignatureAndCompletionTable { get; }
  public IReadOnlyDictionary<Uri, IReadOnlyList<Range>> GhostDiagnostics { get; }
  public IReadOnlyList<ICanVerify>? Verifiables { get; }
  public ConcurrentDictionary<ICanVerify, Unit> VerifyingOrVerifiedSymbols { get; } = new();
  public LazyConcurrentDictionary<ICanVerify, Dictionary<string, ImplementationView>> ImplementationsPerVerifiable { get; } = new();

  /// <summary>
  /// FilePosition is required because the default module lives in multiple files
  /// </summary>
  public LazyConcurrentDictionary<ModuleDefinition, Task<IReadOnlyDictionary<FilePosition, IReadOnlyList<IImplementationTask>>>> TranslatedModules { get; }

  public override IEnumerable<DafnyDiagnostic> GetDiagnostics(Uri uri) {
    var implementationsForUri = ImplementationsPerVerifiable.
      Where(kv => kv.Key.Tok.Uri == uri).
      Select(kv => kv.Value).ToList();
    var verificationDiagnostics = implementationsForUri.SelectMany(view =>
      view.Values.SelectMany(v => v.Diagnostics));
    return base.GetDiagnostics(uri).Concat(verificationDiagnostics);
  }

  public const string OutdatedPrefix = "Outdated: ";
  private IEnumerable<Diagnostic> MarkDiagnosticsAsOutdated(IEnumerable<Diagnostic> diagnostics) {
    return diagnostics.Select(diagnostic => diagnostic with {
      Severity = diagnostic.Severity == DiagnosticSeverity.Error ? DiagnosticSeverity.Warning : diagnostic.Severity,
      Message = diagnostic.Message.StartsWith(OutdatedPrefix)
        ? diagnostic.Message
        : OutdatedPrefix + diagnostic.Message
    });
  }

  VerificationPreparationState MergeStates(VerificationPreparationState a, VerificationPreparationState b) {
    return new[] { a, b }.Max();
  }

  IdeVerificationResult MergeResults(IEnumerable<IdeVerificationResult> results) {
    return results.Aggregate((a, b) => new IdeVerificationResult(
      MergeStates(a.PreparationProgress, b.PreparationProgress),
      a.Implementations.ToImmutableDictionary().Merge(b.Implementations,
        (a, b) => new IdeImplementationView(
          a.Range,
          Combine(a.Status, b.Status),
          a.Diagnostics.Concat(b.Diagnostics).ToList()))));
  }

  public override IdeState ToIdeState(IdeState previousState) {
    IdeVerificationResult MergeVerifiable(ICanVerify canVerify) {
      var range = canVerify.NameToken.GetLspRange();
      var previousImplementations =
        previousState.GetVerificationResults(canVerify.NameToken.Uri).GetValueOrDefault(range)?.Implementations ??
        ImmutableDictionary<string, IdeImplementationView>.Empty;
      if (!ImplementationsPerVerifiable.TryGetValue(canVerify, out var implementationsPerName)) {
        var progress = VerifyingOrVerifiedSymbols.ContainsKey(canVerify)
          ? VerificationPreparationState.InProgress
          : VerificationPreparationState.NotStarted;
        return new IdeVerificationResult(PreparationProgress: progress,
          Implementations: previousImplementations.ToDictionary(kv => kv.Key, kv => kv.Value with {
            Status = PublishedVerificationStatus.Stale,
            Diagnostics = MarkDiagnosticsAsOutdated(kv.Value.Diagnostics).ToList()
          }));
      }

      var implementations = implementationsPerName!.ToDictionary(kv => kv.Key, kv => {
        var implementationView = kv.Value;
        var diagnostics = implementationView.Diagnostics.Select(d => d.ToLspDiagnostic());
        if (implementationView.Status < PublishedVerificationStatus.Error) {
          var previousDiagnostics = previousImplementations.GetValueOrDefault(kv.Key)?.Diagnostics;
          if (previousDiagnostics != null) {
            diagnostics = MarkDiagnosticsAsOutdated(previousDiagnostics);
          }
        }

        // If we're trying to verify this symbol, its status is at least queued.
        var status = implementationView.Status == PublishedVerificationStatus.Stale && VerifyingOrVerifiedSymbols.ContainsKey(canVerify)
          ? PublishedVerificationStatus.Queued : implementationView.Status;
        return new IdeImplementationView(implementationView.Task.Implementation.tok.GetLspRange(true),
          status, diagnostics.ToList());
      });
      return new IdeVerificationResult(VerificationPreparationState.Done, implementations);

    }

    var result = base.ToIdeState(previousState) with {
      SymbolTable = SymbolTable ?? previousState.SymbolTable,
      SignatureAndCompletionTable = SignatureAndCompletionTable.Resolved ? SignatureAndCompletionTable : previousState.SignatureAndCompletionTable,
      GhostRanges = GhostDiagnostics,
      Counterexamples = new List<Counterexample>(Counterexamples),
      ResolutionDiagnostics = ResolutionDiagnostics.ToDictionary(
        kv => kv.Key,
        kv => (IReadOnlyList<Diagnostic>)kv.Value.Select(d => d.ToLspDiagnostic()).ToList()),
      VerificationTrees = VerificationTrees.ToDictionary(kv => kv.Key, kv => (DocumentVerificationTree)kv.Value.GetCopyForNotification()),
      VerificationResults = Verifiables == null ? previousState.VerificationResults : Verifiables.GroupBy(l => l.NameToken.Uri).ToImmutableDictionary(k => k.Key,
        k => k.GroupBy(l => l.NameToken.GetLspRange()).ToDictionary(
          l => l.Key,
          l => MergeResults(l.Select(MergeVerifiable))))
    };
    return result;
  }

  static PublishedVerificationStatus Combine(PublishedVerificationStatus first, PublishedVerificationStatus second) {
    return new[] { first, second }.Min();
  }

  public void RefreshDiagnosticsFromProgramReporter() {
    ResolutionDiagnostics =
      ((DiagnosticErrorReporter)Program.Reporter).AllDiagnosticsCopy;
  }
}
