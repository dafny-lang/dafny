using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Workspace;

using VerifyStatus = Dictionary<string, (IImplementationTask Task, ImplementationView View)>;

public class CompilationAfterResolution : CompilationAfterParsing {

  public CompilationAfterResolution(CompilationAfterParsing compilationAfterParsing,
    IReadOnlyDictionary<Uri, List<DafnyDiagnostic>> diagnostics,
    SymbolTable? symbolTable,
    SignatureAndCompletionTable signatureAndCompletionTable,
    IReadOnlyDictionary<Uri, IReadOnlyList<Range>> ghostDiagnostics,
    Dictionary<ICanVerify, VerifyStatus?> implementationsPerVerifiable,
    ConcurrentDictionary<ModuleDefinition, Task<IReadOnlyDictionary<FilePosition, IReadOnlyList<IImplementationTask>>>> translatedModules,
    List<Counterexample> counterexamples
    ) :
    base(compilationAfterParsing, compilationAfterParsing.Program, diagnostics) {
    SymbolTable = symbolTable;
    SignatureAndCompletionTable = signatureAndCompletionTable;
    GhostDiagnostics = ghostDiagnostics;
    ImplementationsPerVerifiable = implementationsPerVerifiable;
    TranslatedModules = translatedModules;
    Counterexamples = counterexamples;
  }
  public List<Counterexample> Counterexamples { get; set; }
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
      view?.Values.SelectMany(v => v.View.Diagnostics) ?? Enumerable.Empty<DafnyDiagnostic>());
    return base.GetDiagnostics(uri).Concat(verificationDiagnostics);
  }

  public override IdeState ToIdeState(IdeState previousState) {
    IEnumerable<KeyValuePair<ImplementationId, IdeImplementationView>> MergeVerifiable(ICanVerify canVerify) {
      return ImplementationsPerVerifiable[canVerify]?.Select(kv => {
        var implementationId = new ImplementationId(canVerify.Tok.Uri, canVerify.Tok.GetLspPosition(), kv.Key);
        var implementationView = kv.Value.View;
        IEnumerable<Diagnostic> diagnostics = implementationView.Diagnostics.Select(d => d.ToLspDiagnostic());
        if (implementationView.Status < PublishedVerificationStatus.Error) {
          diagnostics = previousState.ImplementationViews.GetValueOrDefault(implementationId)?.Diagnostics ?? diagnostics;
        }

        var value = new IdeImplementationView(implementationView.Range, implementationView.Status, diagnostics.ToList());
        return new KeyValuePair<ImplementationId, IdeImplementationView>(implementationId, value);
      }) ?? previousState.ImplementationViews.Where(kv =>
        kv.Key.Uri == canVerify.Tok.Uri && kv.Key.Position == canVerify.Tok.GetLspPosition());
    }

    return base.ToIdeState(previousState) with {
      SymbolTable = SymbolTable ?? previousState.SymbolTable,
      SignatureAndCompletionTable = SignatureAndCompletionTable.Resolved ? SignatureAndCompletionTable : previousState.SignatureAndCompletionTable,
      GhostRanges = GhostDiagnostics,
      ImplementationsWereUpdated = true,
      Counterexamples = new List<Counterexample>(Counterexamples),
      ImplementationViews = new(ImplementationsPerVerifiable.Keys.SelectMany(MergeVerifiable))
    };
  }

  static PublishedVerificationStatus Combine(PublishedVerificationStatus first, PublishedVerificationStatus second) {
    return new[] { first, second }.Min();
  }
}
