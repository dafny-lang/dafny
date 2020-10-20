using DafnyLS.Language.Symbols;
using Microsoft.Dafny;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace DafnyLS.Language {
  /// <summary>
  /// Internal representation of a dafny document.
  /// </summary>
  public class DafnyDocument {
    public TextDocumentItem Text { get; }
    public DocumentUri Uri => Text.Uri;
    public long Version => Text.Version;

    public Microsoft.Dafny.Program Program { get; }
    public ErrorReporter Errors { get; }
    public CompilationUnit CompilationUnit { get; }
    public SymbolTable SymbolTable { get; }

    public DafnyDocument(
        TextDocumentItem textDocument, ErrorReporter errors, Microsoft.Dafny.Program program, CompilationUnit compilationUnit, SymbolTable symbolTable
    ) {
      Text = textDocument;
      Program = program;
      Errors = errors;
      CompilationUnit = compilationUnit;
      SymbolTable = symbolTable;
    }
  }
}
