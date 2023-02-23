using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public class DocumentAfterResolution : DocumentAfterParsing {
  public DocumentAfterResolution(DocumentTextBuffer textDocumentItem,
    Dafny.Program program,
    IReadOnlyList<DafnyDiagnostic> parseAndResolutionDiagnostics,
    SymbolTable? symbolTable,
    SignatureAndCompletionTable signatureAndCompletionTable,
    IReadOnlyList<Diagnostic> ghostDiagnostics) :
    base(textDocumentItem, program, ImmutableArray<DafnyDiagnostic>.Empty) {
    ParseAndResolutionDiagnostics = parseAndResolutionDiagnostics;
    SymbolTable = symbolTable;
    SignatureAndCompletionTable = signatureAndCompletionTable;
    GhostDiagnostics = ghostDiagnostics;
  }

  public IReadOnlyList<DafnyDiagnostic> ParseAndResolutionDiagnostics { get; }
  public SymbolTable? SymbolTable { get; }
  public SignatureAndCompletionTable SignatureAndCompletionTable { get; }
  public IReadOnlyList<Diagnostic> GhostDiagnostics { get; }

  public override IEnumerable<Diagnostic> Diagnostics => ParseAndResolutionDiagnostics.Select(d => d.ToLspDiagnostic());

  public override IdeState ToIdeState(IdeState previousState) {
    return previousState with {
      TextDocumentItem = TextDocumentItem,
      ImplementationsWereUpdated = false,
      ResolutionDiagnostics = ParseAndResolutionDiagnostics.Select(d => d.ToLspDiagnostic()),
      SymbolTable = SymbolTable ?? previousState.SymbolTable,
      SignatureAndCompletionTable = SignatureAndCompletionTable.Resolved ? SignatureAndCompletionTable : previousState.SignatureAndCompletionTable,
      GhostDiagnostics = GhostDiagnostics
    };
  }
}
