using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using Microsoft.Dafny.LanguageServer.Language;

namespace Microsoft.Dafny.LanguageServer.Workspace;

record ImplementationStateUpdated(ICanVerify CanVerify, string Name, ImplementationState State) : ICompilationEvent {
  public IdeState UpdateState(IdeState previousState) {
    var uri = CanVerify.Tok.Uri;
    var range = CanVerify.NameToken.GetLspRange();
    var previousImplementations = previousState.VerificationResults[uri][range].Implementations;

    // // If we're trying to verify this symbol, its status is at least queued.
    // var status = implementationView.Status == PublishedVerificationStatus.Stale && VerifyingOrVerifiedSymbols.ContainsKey(canVerify)
    //   ? PublishedVerificationStatus.Queued : implementationView.Status;
    var status = State.Status;

    var diagnostics = State.Diagnostics.Select(d => d.ToLspDiagnostic());
    if (status < PublishedVerificationStatus.Error) {
      var previousDiagnostics = previousImplementations.GetValueOrDefault(Name)?.Diagnostics;
      if (previousDiagnostics != null) {
        diagnostics = IdeState.MarkDiagnosticsAsOutdated(previousDiagnostics);
      }
    }

    var newView = new IdeImplementationView(range, status, diagnostics.ToList(), State.HitErrorLimit);

    var previousVerificationResult = previousState.VerificationResults[uri][range];
    return previousState with {
      VerificationResults = previousState.VerificationResults.SetItem(uri, previousState.VerificationResults[uri].SetItem(range, previousVerificationResult with {
        Implementations = previousVerificationResult.Implementations.SetItem(Name, newView)
      }))
    };
  }
}