using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace;

record CanVerifyPartsIdentified(ICanVerify CanVerify, IReadOnlyList<IImplementationTask> Parts) : ICompilationEvent {
  public IdeState UpdateState(DafnyOptions options, ILogger logger, IdeState previousState) {
    var implementations = Parts.Select(t => t.Implementation);
    var gutterIconManager = new GutterIconAndHoverVerificationDetailsManager(logger);
    
    var uri = CanVerify.Tok.Uri;
    var tree = previousState.VerificationTrees.GetValueOrDefault(uri) ?? new DocumentVerificationTree(previousState.Program, uri);
    previousState = previousState with {
      VerificationTrees = previousState.VerificationTrees.SetItem(uri, tree)
    };
    gutterIconManager.ReportImplementationsBeforeVerification(previousState,
      CanVerify, implementations.ToArray());

    var range = CanVerify.NameToken.GetLspRange();
    var previousImplementations = previousState.VerificationResults[uri][range].Implementations;
    var names = Parts.Select(t => CompilationManager.GetImplementationName(t.Implementation));
    var verificationResult = new IdeVerificationResult(PreparationProgress: VerificationPreparationState.Done,
      Implementations: names.ToImmutableDictionary(k => k,
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