using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public class CompilationAfterResolution : CompilationAfterParsing {
  public CompilationAfterResolution(VersionedTextDocumentIdentifier documentIdentifier,
    Program program,
    IReadOnlyDictionary<DocumentUri, List<DafnyDiagnostic>> diagnostics,
    SymbolTable? symbolTable,
    SignatureAndCompletionTable signatureAndCompletionTable,
    IReadOnlyList<Diagnostic> ghostDiagnostics) :
    base(documentIdentifier, program, diagnostics) {
    SymbolTable = symbolTable;
    SignatureAndCompletionTable = signatureAndCompletionTable;
    GhostDiagnostics = ghostDiagnostics;
  }
  public SymbolTable? SymbolTable { get; }
  public SignatureAndCompletionTable SignatureAndCompletionTable { get; }
  public IReadOnlyList<Diagnostic> GhostDiagnostics { get; }

  public override IdeState ToIdeState(IdeState previousState) {
    return base.ToIdeState(previousState) with {
      SymbolTable = SymbolTable ?? previousState.SymbolTable,
      SignatureAndCompletionTable = SignatureAndCompletionTable.Resolved ? SignatureAndCompletionTable : previousState.SignatureAndCompletionTable,
      GhostDiagnostics = GhostDiagnostics
    };
  }
}
