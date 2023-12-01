using System.Collections.Immutable;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Extensions.Logging;

namespace Microsoft.Dafny.LanguageServer.Workspace;

record ScheduledVerification(ICanVerify CanVerify) : ICompilationEvent {

  public Task<IdeState> UpdateState(DafnyOptions options, ILogger logger, IProjectDatabase projectDatabase,
    IdeState previousState) {
    var uri = CanVerify.Tok.Uri;
    var range = CanVerify.NameToken.GetLspRange();
    var previousVerificationResult = previousState.VerificationResults[uri][range];
    var previousImplementations = previousVerificationResult.Implementations;
    var preparationProgress = new[]
      { previousVerificationResult.PreparationProgress, VerificationPreparationState.InProgress }.Max();
    var verificationResult = new IdeVerificationResult(PreparationProgress: preparationProgress,
      Implementations: previousImplementations.ToImmutableDictionary(kv => kv.Key, kv => kv.Value with {
        Status = PublishedVerificationStatus.Stale,
        Diagnostics = IdeState.MarkDiagnosticsAsOutdated(kv.Value.Diagnostics).ToList()
      }));
    return Task.FromResult(previousState with {
      VerificationResults = previousState.VerificationResults.SetItem(uri, previousState.VerificationResults[uri].SetItem(range, verificationResult))
    });
  }
}