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
    Dictionary<ICanVerify, VerifyStatus?> implementationsPerVerifiable,
    ConcurrentDictionary<ModuleDefinition, Task<IReadOnlyDictionary<FilePosition, IReadOnlyList<IImplementationTask>>>> translatedModules,
    List<Counterexample> counterexamples,
    Dictionary<Uri, VerificationTree> verificationTrees
    ) :
    base(compilationAfterParsing, compilationAfterParsing.Program, diagnostics) {
    SymbolTable = symbolTable;
    SignatureAndCompletionTable = signatureAndCompletionTable;
    GhostDiagnostics = ghostDiagnostics;
    ImplementationsPerVerifiable = implementationsPerVerifiable;
    TranslatedModules = translatedModules;
    Counterexamples = counterexamples;
    VerificationTrees = verificationTrees;
  }
  public List<Counterexample> Counterexamples { get; set; }
  public Dictionary<Uri, VerificationTree> VerificationTrees { get; }
  public SymbolTable? SymbolTable { get; }
  public SignatureAndCompletionTable SignatureAndCompletionTable { get; }
  public IReadOnlyDictionary<Uri, IReadOnlyList<Range>> GhostDiagnostics { get; }
  public Dictionary<ICanVerify, VerifyStatus?> ImplementationsPerVerifiable { get; }
  /// <summary>
  /// FilePosition is required because the default module lives in multiple files
  /// </summary>
  public ConcurrentDictionary<ModuleDefinition, Task<IReadOnlyDictionary<FilePosition, IReadOnlyList<IImplementationTask>>>> TranslatedModules { get; }

  public override IEnumerable<DafnyDiagnostic> GetDiagnostics(Uri uri) {
    var implementationsForUri = ImplementationsPerVerifiable.
      Where(kv => kv.Key.Tok.Uri == uri).
      Select(kv => kv.Value).ToList();
    var verificationDiagnostics = implementationsForUri.SelectMany(view =>
      view?.Values.SelectMany(v => v.Diagnostics) ?? Enumerable.Empty<DafnyDiagnostic>());
    return base.GetDiagnostics(uri).Concat(verificationDiagnostics);
  }

  public override IdeState ToIdeState(IdeState previousState) {
    IEnumerable<KeyValuePair<string, IdeImplementationView>> MergeVerifiable(ICanVerify canVerify) {
      var location = canVerify.NameToken.GetLocation();
      var previousForCanVerify = previousState.ImplementationViews.GetValueOrDefault(location) ?? new Dictionary<string, IdeImplementationView>();
      return ImplementationsPerVerifiable[canVerify]?.Select(kv => {
        var implementationView = kv.Value;
        var diagnostics = implementationView.Diagnostics.Select(d => d.ToLspDiagnostic());
        if (implementationView.Status < PublishedVerificationStatus.Error) {
          diagnostics = previousForCanVerify.GetValueOrDefault(kv.Key)?.Diagnostics ?? diagnostics;
        }

        var value = new IdeImplementationView(implementationView.Task.Implementation.tok.GetLspRange(true), implementationView.Status, diagnostics.ToList());
        return new KeyValuePair<string, IdeImplementationView>(kv.Key, value);
      }) ?? previousForCanVerify;
    }

    return base.ToIdeState(previousState) with {
      SymbolTable = SymbolTable ?? previousState.SymbolTable,
      SignatureAndCompletionTable = SignatureAndCompletionTable.Resolved ? SignatureAndCompletionTable : previousState.SignatureAndCompletionTable,
      GhostRanges = GhostDiagnostics,
      ImplementationsWereUpdated = true,
      Counterexamples = new List<Counterexample>(Counterexamples),
      VerificationTrees = VerificationTrees,
      ImplementationViews = ImplementationsPerVerifiable.Keys.GroupBy(l => l.NameToken.GetLocation()).ToDictionary(k => k.Key,
        k => new Dictionary<string, IdeImplementationView>(k.SelectMany(MergeVerifiable)))
    };
  }

  static PublishedVerificationStatus Combine(PublishedVerificationStatus first, PublishedVerificationStatus second) {
    return new[] { first, second }.Min();
  }
}
