using System.Collections.Immutable;
using System.Linq;
using Microsoft.Dafny.LanguageServer.Language;

namespace Microsoft.Dafny.LanguageServer.Workspace;

record ScheduledVerification(ICanVerify CanVerify) : ICompilationEvent {

  public IdeState UpdateState(IdeState previousState) {
    var uri = CanVerify.Tok.Uri;
    var range = CanVerify.NameToken.GetLspRange();
    var previousImplementations = previousState.VerificationResults[uri][range].Implementations;
    var verificationResult = new IdeVerificationResult(PreparationProgress: VerificationPreparationState.InProgress,
      Implementations: previousImplementations.ToImmutableDictionary(kv => kv.Key, kv => kv.Value with {
        Status = PublishedVerificationStatus.Stale,
        Diagnostics = IdeState.MarkDiagnosticsAsOutdated(kv.Value.Diagnostics).ToList()
      }));
    return previousState with {
      VerificationResults = previousState.VerificationResults.SetItem(uri, previousState.VerificationResults[uri].SetItem(range, verificationResult))
    };
  }
}