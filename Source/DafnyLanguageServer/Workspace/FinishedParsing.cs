using System;
using System.Collections.Immutable;
using System.Linq;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace;

record FinishedParsing(
  Program Program,
  ImmutableDictionary<Uri, ImmutableList<Diagnostic>> Diagnostics) : ICompilationEvent 
{
  public IdeState UpdateState(DafnyOptions options, ILogger logger, IdeState previousState) {

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

    return previousState with {
      Program = Program,
      Status = status,
      VerificationTrees = trees
    };
  }
}