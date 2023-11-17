using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace;

record DeterminedRootFiles(
  DafnyProject Project,
  IReadOnlyList<DafnyFile> Roots,
  ImmutableDictionary<Uri, ImmutableList<Diagnostic>> Diagnostics) : ICompilationEvent {
  public async Task<IdeState> UpdateState(DafnyOptions options,
    ILogger logger,
    IProjectDatabase projectDatabase,
    IdeState previousState) {
    var errors = Diagnostics.Values.SelectMany(x => x).
      Where(d => d.Severity == DiagnosticSeverity.Error);
    var status = errors.Any() ? CompilationStatus.ParsingFailed : previousState.Status;

    var ownedUris = new HashSet<Uri>();
    foreach (var file in Roots) {
      var uriProject = await projectDatabase.GetProject(file.Uri);
      var ownedUri = uriProject.Equals(Project);
      if (ownedUri) {
        ownedUris.Add(file.Uri);
      }
    }
    ownedUris.Add(Project.Uri);

    return previousState with {
      OwnedUris = ownedUris,
      StaticDiagnostics = status == CompilationStatus.ParsingFailed ? Diagnostics : previousState.StaticDiagnostics,
      Status = status,
      VerificationTrees = Roots.ToImmutableDictionary(
        file => file.Uri,
        file => previousState.VerificationTrees.GetValueOrDefault(file.Uri) ??
                new DocumentVerificationTree(previousState.Program, file.Uri))
    };
  }
}