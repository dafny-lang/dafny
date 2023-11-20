using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace;

record CanVerifyPartsIdentified(ICanVerify CanVerify, IReadOnlyList<IImplementationTask> Parts) : ICompilationEvent {
  public Task<IdeState> UpdateState(DafnyOptions options, ILogger logger, IProjectDatabase projectDatabase,
    IdeState previousState) {
    var implementations = Parts.Select(t => t.Implementation);
    var gutterIconManager = new GutterIconAndHoverVerificationDetailsManager(logger);

    var uri = CanVerify.Tok.Uri;
    gutterIconManager.ReportImplementationsBeforeVerification(previousState,
      CanVerify, implementations.ToArray());

    var range = CanVerify.NameToken.GetLspRange();
    var previousImplementations = previousState.VerificationResults[uri][range].Implementations;
    var names = Parts.Select(t => Compilation.GetImplementationName(t.Implementation));
    var verificationResult = new IdeVerificationResult(PreparationProgress: VerificationPreparationState.Done,
      Implementations: names.ToImmutableDictionary(k => k,
        k => {
          var previous = previousImplementations.GetValueOrDefault(k);
          return new IdeImplementationView(range, PublishedVerificationStatus.Queued,
            previous?.Diagnostics ?? Array.Empty<Diagnostic>(),
            previous?.HitErrorLimit ?? false);
        }));
    return Task.FromResult(previousState with {
      VerificationResults = previousState.VerificationResults.SetItem(uri, previousState.VerificationResults[uri].SetItem(range, verificationResult))
    });
  }
}