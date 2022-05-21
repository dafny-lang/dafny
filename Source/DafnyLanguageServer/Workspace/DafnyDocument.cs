using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using Microsoft.Boogie;
using SymbolTable = Microsoft.Dafny.LanguageServer.Language.Symbols.SymbolTable;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;

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
    IReadOnlyDictionary<ImplementationId, IReadOnlyList<Diagnostic>> VerificationDiagnosticsPerImplementation,
    IReadOnlyList<Counterexample> CounterExamples,
    IReadOnlyList<Diagnostic> GhostDiagnostics,
    Dafny.Program Program,
    SymbolTable SymbolTable,

    bool LoadCanceled = false
  ) {

    public IEnumerable<Diagnostic> Diagnostics => ParseAndResolutionDiagnostics.Concat(VerificationDiagnosticsPerImplementation.SelectMany(kv => kv.Value));

    public DocumentUri Uri => TextDocumentItem.Uri;
    public int Version => TextDocumentItem.Version!.Value;


    /// <summary>
    /// Contains the real-time status of all verification efforts.
    /// Can be migrated from a previous document
    /// The position and the range are never sent to the client.
    /// </summary>
    public VerificationTree VerificationTree { get; init; } = new DocumentVerificationTree(
      TextDocumentItem.Uri.ToString(),
      TextDocumentItem.Text.Count(c => c == '\n') + 1
    );

    // List of a few last touched method positions
    public ImmutableList<Position> LastTouchedMethodPositions { get; set; } = new List<Position>() { }.ToImmutableList();

    // Used to prioritize verification to one method and its dependencies
    public Range? LastChange { get; init; } = null;

    /// <summary>
    /// Checks if the given document uri is pointing to this dafny document.
    /// </summary>
    /// <param name="documentUri">The document uri to check.</param>
    /// <returns><c>true</c> if the specified document uri points to the file represented by this document.</returns>
    public bool IsDocument(DocumentUri documentUri) {
      return documentUri == Uri;
    }

    public int LinesCount => VerificationTree.Range.End.Line;
  }
}
