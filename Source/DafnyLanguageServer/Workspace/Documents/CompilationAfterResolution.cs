using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Workspace;

using VerifyStatus = Dictionary<string, ImplementationView>;

public class CompilationAfterResolution : CompilationAfterParsing {

  public CompilationAfterResolution(CompilationAfterParsing compilationAfterParsing,
    IReadOnlyDictionary<Uri, List<DafnyDiagnostic>> diagnostics,
    SymbolTable? symbolTable,
    SignatureAndCompletionTable signatureAndCompletionTable,
    IReadOnlyDictionary<Uri, IReadOnlyList<Range>> ghostDiagnostics,
    IReadOnlyList<ICanVerify> verifiables,
    ConcurrentDictionary<ModuleDefinition, Task<IReadOnlyDictionary<FilePosition, IReadOnlyList<IImplementationTask>>>> translatedModules,
    List<Counterexample> counterexamples
    ) :
    base(compilationAfterParsing, compilationAfterParsing.Program, diagnostics, compilationAfterParsing.VerificationTrees) {
    SymbolTable = symbolTable;
    SignatureAndCompletionTable = signatureAndCompletionTable;
    GhostDiagnostics = ghostDiagnostics;
    Verifiables = verifiables;
    TranslatedModules = translatedModules;
    Counterexamples = counterexamples;
  }
  public List<Counterexample> Counterexamples { get; set; }
  public SymbolTable? SymbolTable { get; }
  public SignatureAndCompletionTable SignatureAndCompletionTable { get; }
  public IReadOnlyDictionary<Uri, IReadOnlyList<Range>> GhostDiagnostics { get; }
  public IReadOnlyList<ICanVerify> Verifiables { get; }
  public ConcurrentDictionary<ICanVerify, VerifyStatus> ImplementationsPerVerifiable { get; } = new();
  /// <summary>
  /// FilePosition is required because the default module lives in multiple files
  /// </summary>
  public ConcurrentDictionary<ModuleDefinition, Task<IReadOnlyDictionary<FilePosition, IReadOnlyList<IImplementationTask>>>> TranslatedModules { get; }

  public override IEnumerable<DafnyDiagnostic> GetDiagnostics(Uri uri) {
    var implementationsForUri = ImplementationsPerVerifiable.
      Where(kv => kv.Key.Tok.Uri == uri).
      Select(kv => kv.Value).ToList();
    var verificationDiagnostics = implementationsForUri.SelectMany(view =>
      view.Values.SelectMany(v => v.Diagnostics) ?? Enumerable.Empty<DafnyDiagnostic>());
    return base.GetDiagnostics(uri).Concat(verificationDiagnostics);
  }

  public const string OutdatedPrefix = "Outdated: ";
  private IEnumerable<Diagnostic> MarkDiagnosticsAsOutdated(IEnumerable<Diagnostic> diagnostics) {
    return diagnostics.Select(diagnostic => diagnostic with {
      Severity = diagnostic.Severity == DiagnosticSeverity.Error ? DiagnosticSeverity.Warning : diagnostic.Severity,
      Message = diagnostic.Message.StartsWith(OutdatedPrefix)
        ? diagnostic.Message
        : OutdatedPrefix + diagnostic.Message
    });
  }

  public override IdeState ToIdeState(IdeState previousState) {
    IEnumerable<KeyValuePair<string, IdeImplementationView>> MergeVerifiable(ICanVerify canVerify) {
      var location = canVerify.NameToken.GetLocation();
      var previousForCanVerify = previousState.ImplementationViews.GetValueOrDefault(location) ?? new Dictionary<string, IdeImplementationView>();
      if (!ImplementationsPerVerifiable.TryGetValue(canVerify, out var implementationsPerName)) {
        return previousForCanVerify.ToDictionary(kv => kv.Key, kv => kv.Value with {
          Status = PublishedVerificationStatus.Stale,
          Diagnostics = MarkDiagnosticsAsOutdated(kv.Value.Diagnostics).ToList()
        });
      }

      return implementationsPerName.Select(kv => {
        var implementationView = kv.Value;
        var diagnostics = implementationView.Diagnostics.Select(d => d.ToLspDiagnostic());
        if (implementationView.Status < PublishedVerificationStatus.Error) {
          var previousDiagnostics = previousForCanVerify.GetValueOrDefault(kv.Key)?.Diagnostics;
          if (previousDiagnostics != null) {
            diagnostics = MarkDiagnosticsAsOutdated(previousDiagnostics);
          }
        }

        var value = new IdeImplementationView(implementationView.Task.Implementation.tok.GetLspRange(true),
          implementationView.Status, diagnostics.ToList());
        return new KeyValuePair<string, IdeImplementationView>(kv.Key, value);
      });

    }

    return base.ToIdeState(previousState) with {
      SymbolTable = SymbolTable ?? previousState.SymbolTable,
      SignatureAndCompletionTable = SignatureAndCompletionTable.Resolved ? SignatureAndCompletionTable : previousState.SignatureAndCompletionTable,
      GhostRanges = GhostDiagnostics,
      Counterexamples = new List<Counterexample>(Counterexamples),
      VerificationTrees = VerificationTrees,
      ImplementationViews = Verifiables.GroupBy(l => l.NameToken.GetLocation()).ToDictionary(k => k.Key,
        k => new Dictionary<string, IdeImplementationView>(k.SelectMany(MergeVerifiable)))
    };
  }

  static PublishedVerificationStatus Combine(PublishedVerificationStatus first, PublishedVerificationStatus second) {
    return new[] { first, second }.Min();
  }
}
