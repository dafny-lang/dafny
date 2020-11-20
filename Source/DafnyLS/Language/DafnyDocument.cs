﻿using Microsoft.Dafny.LanguageServer.Language.Symbols;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Language {
  /// <summary>
  /// Internal representation of a dafny document.
  /// </summary>
  public class DafnyDocument {
    public TextDocumentItem Text { get; }
    public DocumentUri Uri => Text.Uri;
    public long Version => Text.Version;

    public Dafny.Program Program { get; }
    public ErrorReporter Errors { get; }
    public SymbolTable SymbolTable { get; }

    /// <summary>
    /// Gets the counter example if the verifier reported issues. <c>null</c> if there
    /// are no verification errors.
    /// </summary>
    public string? CounterExample { get; }

    public DafnyDocument(
        TextDocumentItem textDocument,
        ErrorReporter errors,
        Dafny.Program program,
        SymbolTable symbolTable,
        string? counterExample
    ) {
      Text = textDocument;
      Program = program;
      Errors = errors;
      SymbolTable = symbolTable;
      CounterExample = counterExample;
    }


    /// <summary>
    /// Checks if the specified token is part of this document.
    /// </summary>
    /// <param name="token">The token to check.</param>
    /// <returns><c>true</c> if the given token belongs to this document.</returns>
    public bool IsPartOf(Microsoft.Boogie.IToken token) {
      return Program.IsPartOfEntryDocument(token);
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
