using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public class CompilationAfterTranslation : CompilationAfterResolution {
  public CompilationAfterTranslation(
    IServiceProvider services,
    CompilationAfterResolution compilationAfterResolution,
    IReadOnlyDictionary<Uri, List<DafnyDiagnostic>> diagnostics,
    IReadOnlyList<IImplementationTask> verificationTasks,
    List<Counterexample> counterexamples,
    Dictionary<ImplementationId, ImplementationView> implementationIdToView
    // , VerificationTree verificationTree
    )
    : base(compilationAfterResolution, diagnostics,
      compilationAfterResolution.SymbolTable, compilationAfterResolution.SignatureAndCompletionTable,
      compilationAfterResolution.GhostDiagnostics) {
    // VerificationTree = verificationTree;
    VerificationTasks = verificationTasks;
    Counterexamples = counterexamples;
    ImplementationIdToView = implementationIdToView;

    GutterProgressReporter = new VerificationProgressReporter(
      services.GetRequiredService<ILogger<VerificationProgressReporter>>(),
      this,
      services.GetRequiredService<INotificationPublisher>(),
      services.GetRequiredService<DafnyOptions>());
  }

  // public override VerificationTree GetInitialDocumentVerificationTree() {
  //   return VerificationTree;
  // }

  public override IEnumerable<DafnyDiagnostic> GetDiagnostics(Uri uri) {
    var views = ImplementationIdToView.Where(kv => kv.Key.Uri == uri).ToList();
    return base.GetDiagnostics(uri).Concat(views.SelectMany(view => view.Value.Diagnostics));
  }

  public override ImmutableDictionary<TextDocumentIdentifier, VerificationTree> GetVerificationTrees() {
    throw new Exception();
    // return VerificationTree;
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
      // VerificationTree = VerificationTree,
      Counterexamples = new List<Counterexample>(Counterexamples),
      ImplementationIdToView = new Dictionary<ImplementationId, IdeImplementationView>(implementationViewsWithMigratedDiagnostics)
    };
  }

  public override IEnumerable<DafnyDiagnostic> AllFileDiagnostics => base.AllFileDiagnostics.Concat(
    ImplementationIdToView.SelectMany(kv => kv.Value.Diagnostics));

  /// <summary>
  /// Contains the real-time status of all verification efforts.
  /// Can be migrated from a previous document
  /// The position and the range are never sent to the client.
  /// </summary>
  public VerificationTree VerificationTree { get; set; }
  public IReadOnlyList<IImplementationTask> VerificationTasks { get; set; }
  public IVerificationProgressReporter GutterProgressReporter { get; set; }
  public List<Counterexample> Counterexamples { get; set; }
  public Dictionary<ImplementationId, ImplementationView> ImplementationIdToView { get; set; }
}