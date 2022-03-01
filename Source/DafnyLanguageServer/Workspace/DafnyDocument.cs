using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Text.RegularExpressions;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Internal representation of a dafny document.
  /// </summary>
  /// <param name="Text">The text document represented by this dafny document.</param>
  /// <param name="Errors">The diagnostics to report.</param>
  /// <param name="GhostDiagnostics">The ghost state diagnostics of the document.</param>
  /// <param name="Program">The compiled Dafny program.</param>
  /// <param name="SymbolTable">The symbol table for the symbol lookups.</param>
  /// <param name="LoadCanceled"><c>true</c> if the document load was canceled for this document.</param>
  public record DafnyDocument(
    TextDocumentItem Text,
    DiagnosticErrorReporter Errors,
    IReadOnlyList<Diagnostic> OldVerificationDiagnostics,
    IReadOnlyList<Diagnostic> GhostDiagnostics,
    Dafny.Program Program,
    SymbolTable SymbolTable,
    bool LoadCanceled = false
  ) {
    public DocumentUri Uri => Text.Uri;
    public int Version => Text.Version!.Value;

    /// <summary>
    /// Gets the serialized models of the counter examples if the verifier reported issues.
    /// <c>null</c> if there are no verification errors or no verification was run.
    /// </summary>
    public string? SerializedCounterExamples { get; init; }


    /// <summary>
    /// True is the resolution succeeded, false if resolution failed
    /// <c>null</c> If the verification did not start (e.g. because of resolution errors)
    /// </summary>
    public bool? ResolutionSucceeded { get; set; } = null;

    /// <summary>
    /// True is the verification pass went through, false if it failed because of verification errors
    /// <c>null</c> If the verification did not start (e.g. because of resolution errors or verification deactivated)
    /// </summary>
    public bool? VerificationPass { get; set; } = null;

    /// <summary>
    /// Contains the real-time status of all verification efforts.
    /// Can be migrated from a previous document
    /// The position and the range are never sent to the client.
    /// </summary>
    public NodeDiagnostic VerificationNodeDiagnostic { get; init; } = new NodeDiagnostic(
      "Document",
      Text.Uri.ToString(),
      Text.Uri.ToString(),
      new Position(0, 0),
      new Range(new Position(0, 0),
        new Position(Regex.Matches(Text.Text, "\r?\n").Count + 1, 0)),
      true
    );

    // List of last 5 top-level touched verification diagnostics positions
    public List<Position> LastTouchedMethods { get; init; } = new();

    // Used to prioritize verification to one method and its dependencies
    public Range? LastChange { get; set; } = null;

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
