using Microsoft.Dafny.LanguageServer.Language;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Linq;
using System.Reactive.Linq;
using System.Threading.Tasks;
using DafnyServer;
using Microsoft.Boogie;
using VCGeneration;
using SymbolTable = Microsoft.Dafny.LanguageServer.Language.Symbols.SymbolTable;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Internal representation of a dafny document.
  /// </summary>
  /// <param name="TextDocumentItem">The text document represented by this dafny document.</param>
  /// <param name="Errors">The diagnostics to report.</param>
  /// <param name="GhostDiagnostics">The ghost state diagnostics of the document.</param>
  /// <param name="Program">The compiled Dafny program.</param>
  /// <param name="SymbolTable">The symbol table for the symbol lookups.</param>
  /// <param name="LoadCanceled"><c>true</c> if the document load was canceled for this document.</param>
  public record DafnyDocument(
    DafnyOptions Options,
    TextDocumentItem TextDocumentItem,
    IReadOnlyList<Diagnostic> ParseAndResolutionDiagnostics,
    // VerificationDiagnostics can be deduced from CounterExamples,
    // but they are stored separately because they are migrated and counterexamples currently are not.
    IReadOnlyDictionary<string, IReadOnlyList<Diagnostic>> VerificationDiagnostics,
    IReadOnlyList<Counterexample> CounterExamples,
    IReadOnlyList<Diagnostic> GhostDiagnostics,
    Dafny.Program Program,
    SymbolTable SymbolTable,
    bool LoadCanceled = false
  ) {

    public IEnumerable<Diagnostic> Diagnostics => ParseAndResolutionDiagnostics.Concat(VerificationDiagnostics.SelectMany(kv => kv.Value));

    public DocumentUri Uri => TextDocumentItem.Uri;
    public int Version => TextDocumentItem.Version!.Value;

    /// <summary>
    /// Checks if the given document uri is pointing to this dafny document.
    /// </summary>
    /// <param name="documentUri">The document uri to check.</param>
    /// <returns><c>true</c> if the specified document uri points to the file represented by this document.</returns>
    public bool IsDocument(DocumentUri documentUri) {
      return documentUri == Uri;
    }
  }
}
