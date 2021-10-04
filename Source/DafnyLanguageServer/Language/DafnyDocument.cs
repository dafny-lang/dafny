using Microsoft.Dafny.LanguageServer.Language.Symbols;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;

namespace Microsoft.Dafny.LanguageServer.Language {
  /// <summary>
  /// Internal representation of a dafny document.
  /// </summary>
  public class DafnyDocument {
    public TextDocumentItem Text { get; }
    public DocumentUri Uri => Text.Uri;
    public int Version => Text.Version!.Value;

    public Dafny.Program Program { get; }
    public DiagnosticErrorReporter Errors { get; }
    public SymbolTable SymbolTable { get; }

    /// <summary>
    /// <c>true</c> if the document load was canceled for this document.
    /// </summary>
    public bool LoadCanceled { get; }

    /// <summary>
    /// Gets the serialized models of the counter examples if the verifier reported issues.
    /// <c>null</c> if there are no verification errors.
    /// </summary>
    public string? SerializedCounterExamples { get; }

    /// <summary>
    /// Gets the ghost diagnostics for this document.
    /// </summary>
    public IReadOnlyList<Diagnostic> GhostDiagnostics { get; }

    public DafnyDocument(
      TextDocumentItem textDocument,
      DiagnosticErrorReporter errors,
      IReadOnlyList<Diagnostic> ghostDiagnostics,
      Dafny.Program program,
      SymbolTable symbolTable,
      string? serializedCounterExamples,
      bool loadCanceled = false
    ) {
      Text = textDocument;
      GhostDiagnostics = ghostDiagnostics;
      Errors = errors;
      Program = program;
      SymbolTable = symbolTable;
      SerializedCounterExamples = serializedCounterExamples;
      LoadCanceled = loadCanceled;
    }

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
