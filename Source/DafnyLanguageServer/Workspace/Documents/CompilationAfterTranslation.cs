using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public class CompilationAfterTranslation : CompilationAfterResolution {
  public CompilationAfterTranslation(
    CompilationAfterResolution compilationAfterResolution,
    IReadOnlyDictionary<Uri, List<DafnyDiagnostic>> diagnostics,
    IReadOnlyList<IImplementationTask> verificationTasks,
    List<Counterexample> counterexamples,
    Dictionary<ImplementationId, ImplementationView> implementationIdToView,
    Dictionary<Uri, VerificationTree> verificationTrees
    )
    : base(compilationAfterResolution, diagnostics,
      compilationAfterResolution.SymbolTable, compilationAfterResolution.SignatureAndCompletionTable,
      compilationAfterResolution.GhostDiagnostics) {
    VerificationTrees = verificationTrees;
    VerificationTasks = verificationTasks;
    Counterexamples = counterexamples;
    ImplementationIdToView = implementationIdToView;
  }

  public override VerificationTree GetVerificationTree(Uri uri) {
    return VerificationTrees[uri];
  }

  public override IEnumerable<DafnyDiagnostic> GetDiagnostics(Uri uri) {
    var views = ImplementationIdToView.Where(kv => kv.Key.Uri == uri).ToList();
    return base.GetDiagnostics(uri).Concat(views.SelectMany(view => view.Value.Diagnostics));
  }

  public override IdeState ToIdeState(IdeState previousState) {
    IEnumerable<KeyValuePair<ImplementationId, IdeImplementationView>> implementationViewsWithMigratedDiagnostics = ImplementationIdToView.Select(kv => {
      IEnumerable<Diagnostic> diagnostics = kv.Value.Diagnostics.Select(d => Util.ToLspDiagnostic(d));
      if (kv.Value.Status < PublishedVerificationStatus.Error) {
        diagnostics = previousState.ImplementationIdToView.GetValueOrDefault(kv.Key)?.Diagnostics ?? diagnostics;
      }

      var value = new IdeImplementationView(kv.Value.Range, kv.Value.Status, diagnostics.ToList());
      return new KeyValuePair<ImplementationId, IdeImplementationView>(kv.Key, value);
    });
    return base.ToIdeState(previousState) with {
      ImplementationsWereUpdated = true,
      VerificationTrees = VerificationTrees.ToDictionary(kv => kv.Key, kv => kv.Value.GetCopyForNotification()),
      Counterexamples = new List<Counterexample>(Counterexamples),
      ImplementationIdToView = new Dictionary<ImplementationId, IdeImplementationView>(implementationViewsWithMigratedDiagnostics)
    };
  }

  public IReadOnlyList<IImplementationTask> VerificationTasks { get; set; }
  /// <summary>
  /// Contains the real-time status of all verification efforts.
  /// Can be migrated from a previous document
  /// The position and the range are never sent to the client.
  /// </summary>
  public Dictionary<Uri, VerificationTree> VerificationTrees { get; set; }
  public List<Counterexample> Counterexamples { get; set; }
  public Dictionary<ImplementationId, ImplementationView> ImplementationIdToView { get; set; }
}