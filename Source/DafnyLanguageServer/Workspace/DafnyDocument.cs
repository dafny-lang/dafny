using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;

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
    /// Checks if the given document uri is pointing to this dafny document.
    /// </summary>
    /// <param name="documentUri">The document uri to check.</param>
    /// <returns><c>true</c> if the specified document uri points to the file represented by this document.</returns>
    public bool IsDocument(DocumentUri documentUri) {
      return documentUri == Uri;
    }
  }
}
