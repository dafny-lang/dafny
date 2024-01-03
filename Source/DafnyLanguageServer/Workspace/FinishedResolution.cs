using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Workspace;

record FinishedResolution(
  ImmutableDictionary<Uri, ImmutableList<Diagnostic>> Diagnostics,
  Program ResolvedProgram,
  SymbolTable? SymbolTable,
  LegacySignatureAndCompletionTable LegacySignatureAndCompletionTable,
  IReadOnlyDictionary<Uri, IReadOnlyList<Range>> GhostRanges,
  IReadOnlyList<ICanVerify>? CanVerifies) : ICompilationEvent {
  public Task<IdeState> UpdateState(DafnyOptions options, ILogger logger, IProjectDatabase projectDatabase,
    IdeState previousState) {
    var errors = Diagnostics.Values.SelectMany(x => x).
      Where(d => d.Severity == DiagnosticSeverity.Error && d.Source != MessageSource.Compiler.ToString()).ToList();
    var status = errors.Any() ? CompilationStatus.ResolutionFailed : CompilationStatus.ResolutionSucceeded;

    var trees = previousState.VerificationTrees;
    if (status == CompilationStatus.ResolutionSucceeded) {
      foreach (var uri in trees.Keys) {
        trees = trees.SetItem(uri,
          GutterIconAndHoverVerificationDetailsManager.UpdateTree(options, ResolvedProgram,
            previousState.VerificationTrees[uri]));
      }
    }

    var verificationResults = CanVerifies == null
      ? previousState.VerificationResults
      : CanVerifies.GroupBy(l => l.NameToken.Uri).ToImmutableDictionary(k => k.Key,
        k => k.GroupBy<ICanVerify, Range>(l => l.NameToken.GetLspRange()).ToImmutableDictionary(
          l => l.Key,
          l => MergeResults(l.Select(canVerify => MergeVerifiable(previousState, canVerify)))));
    var signatureAndCompletionTable = LegacySignatureAndCompletionTable.Resolved ? LegacySignatureAndCompletionTable : previousState.SignatureAndCompletionTable;

    return Task.FromResult(previousState with {
      StaticDiagnostics = Diagnostics,
      Status = status,
      ResolvedProgram = ResolvedProgram,
      SymbolTable = SymbolTable ?? previousState.SymbolTable,
      SignatureAndCompletionTable = signatureAndCompletionTable,
      GhostRanges = GhostRanges,
      Counterexamples = new List<Counterexample>(),
      VerificationResults = verificationResults,
      VerificationTrees = trees
    });
  }

  private static IdeVerificationResult MergeResults(IEnumerable<IdeVerificationResult> results) {
    return results.Aggregate((a, b) => new IdeVerificationResult(
      MergeStates(a.PreparationProgress, b.PreparationProgress),
      a.Implementations.ToImmutableDictionary().Merge(b.Implementations,
        (aView, bView) => new IdeImplementationView(
          aView.Range,
          Combine(aView.Status, bView.Status),
          aView.Diagnostics.Concat(bView.Diagnostics).ToList(), aView.HitErrorLimit || bView.HitErrorLimit))));
  }

  private static VerificationPreparationState MergeStates(VerificationPreparationState a, VerificationPreparationState b) {
    return new[] { a, b }.Max();
  }

  private static PublishedVerificationStatus Combine(PublishedVerificationStatus first, PublishedVerificationStatus second) {
    return new[] { first, second }.Min();
  }

  private static IdeVerificationResult MergeVerifiable(IdeState previousState, ICanVerify canVerify) {
    var range = canVerify.NameToken.GetLspRange();
    var previousImplementations =
      previousState.GetVerificationResults(canVerify.NameToken.Uri).GetValueOrDefault(range)?.Implementations ??
      ImmutableDictionary<string, IdeImplementationView>.Empty;
    return new IdeVerificationResult(PreparationProgress: VerificationPreparationState.NotStarted,
      Implementations: previousImplementations.ToImmutableDictionary(kv => kv.Key, kv => kv.Value with {
        Status = PublishedVerificationStatus.Stale,
        Diagnostics = IdeState.MarkDiagnosticsAsOutdated(kv.Value.Diagnostics).ToList()
      }));
  }
}