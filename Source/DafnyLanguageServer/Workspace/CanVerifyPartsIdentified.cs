using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using Microsoft.Dafny.LanguageServer.Language;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace;

record CanVerifyPartsIdentified(ICanVerify CanVerify, ICollection<string> Parts) : ICompilationEvent {
  public IdeState UpdateState(IdeState previousState) {
    var uri = CanVerify.Tok.Uri;
    var range = CanVerify.NameToken.GetLspRange();
    var previousImplementations = previousState.VerificationResults[uri][range].Implementations;
    var verificationResult = new IdeVerificationResult(PreparationProgress: VerificationPreparationState.Done,
      Implementations: Parts.ToImmutableDictionary(k => k,
        k => {
          var previous = previousImplementations.GetValueOrDefault(k);
          return new IdeImplementationView(range, PublishedVerificationStatus.Stale, 
            IdeState.MarkDiagnosticsAsOutdated(previous?.Diagnostics ?? Enumerable.Empty<Diagnostic>()).ToList(),
            previous?.HitErrorLimit ?? false);
        }));
    return previousState with {
      VerificationResults = previousState.VerificationResults.SetItem(uri, previousState.VerificationResults[uri].SetItem(range, verificationResult))
    };
  }
}