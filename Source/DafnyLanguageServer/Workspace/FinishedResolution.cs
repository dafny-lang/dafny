using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Workspace;

record FinishedResolution(
  CompilationAfterResolution Compilation,
  SymbolTable? SymbolTable,
  LegacySignatureAndCompletionTable LegacySignatureAndCompletionTable,
  IReadOnlyDictionary<Uri, IReadOnlyList<Range>> GhostRanges,
  IReadOnlyList<ICanVerify>? CanVerifies) : ICompilationEvent {
  public IdeState UpdateState(IdeState previousState) {
    var verificationResults = CanVerifies == null
      ? previousState.VerificationResults
      : CanVerifies.GroupBy(l => l.NameToken.Uri).ToImmutableDictionary(k => k.Key,
        k => k.GroupBy<ICanVerify, Range>(l => l.NameToken.GetLspRange()).ToImmutableDictionary(
          l => l.Key,
          l => MergeResults(l.Select(canVerify => MergeVerifiable(previousState, canVerify)))));
    return previousState with {
      Compilation = Compilation,
      SymbolTable = SymbolTable
                    ?? previousState.SymbolTable, // TODO migration seems missing
      SignatureAndCompletionTable = LegacySignatureAndCompletionTable,
      GhostRanges = GhostRanges,
      VerificationResults = verificationResults
    };
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
    var progress = VerificationPreparationState.NotStarted;
    return new IdeVerificationResult(PreparationProgress: progress,
      Implementations: previousImplementations.ToImmutableDictionary(kv => kv.Key, kv => kv.Value with {
        Status = PublishedVerificationStatus.Stale,
        Diagnostics = IdeState.MarkDiagnosticsAsOutdated(kv.Value.Diagnostics).ToList()
      }));
  }
}