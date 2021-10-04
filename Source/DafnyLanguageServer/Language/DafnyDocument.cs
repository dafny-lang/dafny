using Microsoft.Dafny.LanguageServer.Language.Symbols;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;

namespace Microsoft.Dafny.LanguageServer.Language {
  /// <summary>
  /// Internal representation of a dafny document.
  /// </summary>
  /// <param name="Text">The text document represented by this dafny document.</param>
  /// <param name="Errors">The error reporter used when parsing/resolving/verifiying the dafny program.</param>
  /// <param name="GhostDiagnostics">The ghost state diagnostics of the document.</param>
  /// <param name="Program">The compiled dafny program.</param>
  /// <param name="SerializedCounterExamples">
  /// Gets the serialized models of the counter examples if the verifier reported issues.
  /// <c>null</c> if there are no verification errors.
  /// </param>
  /// <param name="LoadCanceled"><c>true</c> if the document load was canceled for this document.</param>
  public record DafnyDocument(
    TextDocumentItem Text,
    DiagnosticErrorReporter Errors,
    IReadOnlyList<Diagnostic> GhostDiagnostics,
    Dafny.Program Program,
    SymbolTable SymbolTable,
    string? SerializedCounterExamples,
    bool LoadCanceled = false
  ) {
    public DocumentUri Uri => Text.Uri;
    public int Version => Text.Version!.Value;

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
