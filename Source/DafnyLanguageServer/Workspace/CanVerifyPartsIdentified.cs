using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace;

record CanVerifyPartsIdentified(ICanVerify CanVerify, IReadOnlyList<IImplementationTask> Parts) : ICompilationEvent {
  public IdeState UpdateState(DafnyOptions options, ILogger logger, IdeState previousState) {

    var implementations = Parts.Select(t => t.Implementation);
    var gutterIconManager = new GutterIconAndHoverVerificationDetailsManager(logger);
    gutterIconManager.ReportImplementationsBeforeVerification(previousState,
      CanVerify, implementations.ToArray());
    
    
    var uri = CanVerify.Tok.Uri;
    var range = CanVerify.NameToken.GetLspRange();
    var previousImplementations = previousState.VerificationResults[uri][range].Implementations;
    var verificationResult = new IdeVerificationResult(PreparationProgress: VerificationPreparationState.Done,
      Implementations: Parts.Select(t => t.Implementation.Name).ToImmutableDictionary(k => k,
        k => {
          var previous = previousImplementations.GetValueOrDefault(k);
          return new IdeImplementationView(range, PublishedVerificationStatus.Stale, 
            previous?.Diagnostics ?? Array.Empty<Diagnostic>(),
            previous?.HitErrorLimit ?? false);
        }));
    return previousState with {
      VerificationResults = previousState.VerificationResults.SetItem(uri, previousState.VerificationResults[uri].SetItem(range, verificationResult))
    };
  }
}