using System;
using System.Collections.Immutable;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace;

record FinishedParsing(
  Program Program,
  ImmutableDictionary<Uri, ImmutableList<Diagnostic>> Diagnostics) : ICompilationEvent {
  public Task<IdeState> UpdateState(DafnyOptions options, ILogger logger, IProjectDatabase projectDatabase,
    IdeState previousState) {

    var trees = previousState.VerificationTrees;
    foreach (var uri in trees.Keys) {
      trees = trees.SetItem(uri,
        new DocumentVerificationTree(Program, uri) {
          Children = trees[uri].Children
        });
    }

    var errors = Diagnostics.Values.SelectMany(x => x).
      Where(d => d.Severity == DiagnosticSeverity.Error);
    var status = errors.Any() ? CompilationStatus.ParsingFailed : CompilationStatus.ResolutionStarted;

    return Task.FromResult(previousState with {
      Program = Program,
      StaticDiagnostics = status == CompilationStatus.ParsingFailed ? Diagnostics : previousState.StaticDiagnostics,
      Status = status,
      VerificationTrees = trees
    });
  }
}