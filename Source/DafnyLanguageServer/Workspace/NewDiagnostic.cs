using System;
using System.Collections.Immutable;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public record NewDiagnostic(Uri Uri, DafnyDiagnostic Diagnostic) : ICompilationEvent {
  public Task<IdeState> UpdateState(DafnyOptions options, ILogger logger, IProjectDatabase projectDatabase,
    IdeState previousState) {
    // Until resolution is finished, keep showing the old diagnostics. 
    if (previousState.Status > CompilationStatus.ResolutionStarted) {
      var diagnostics = previousState.StaticDiagnostics.GetValueOrDefault(Uri, ImmutableList<Diagnostic>.Empty);
      var newDiagnostics = diagnostics.Add(Diagnostic.ToLspDiagnostic());
      return Task.FromResult(previousState with {
        StaticDiagnostics = previousState.StaticDiagnostics.SetItem(Uri, newDiagnostics)
      });
    }

    return Task.FromResult(previousState);

  }
}