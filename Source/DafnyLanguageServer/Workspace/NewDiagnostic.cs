using System;
using System.Collections.Immutable;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public record NewDiagnostic(Uri Uri, DafnyDiagnostic Diagnostic) : ICompilationEvent {
  public IdeState UpdateState(DafnyOptions options, ILogger logger, IdeState previousState) {
    if (previousState.Compilation is CompilationAfterResolution) {
      var diagnostics = previousState.StaticDiagnostics.GetValueOrDefault(Uri, ImmutableList<Diagnostic>.Empty);
      var newDiagnostics = diagnostics.Add(Diagnostic.ToLspDiagnostic());
      return previousState with {
          StaticDiagnostics = previousState.StaticDiagnostics.SetItem(Uri, newDiagnostics)
        };
    }

    return previousState;

  }
}