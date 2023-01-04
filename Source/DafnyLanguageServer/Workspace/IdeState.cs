using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace;

/// <summary>
/// Contains information from the latest document, and from older documents if some information is missing,
/// to provide the IDE with as much information as possible.
/// </summary>
public record IdeState(
  DocumentTextBuffer TextDocumentItem,
  IEnumerable<Diagnostic> ResolutionDiagnostics,
  SymbolTable SymbolTable,
  SignatureAndCompletionTable SignatureAndCompletionTable,
  IReadOnlyDictionary<ImplementationId, ImplementationView> ImplementationIdToView,
  IReadOnlyList<Counterexample> Counterexamples,
  bool ImplementationsWereUpdated,
  IEnumerable<Diagnostic> GhostDiagnostics,
  VerificationTree VerificationTree
) {

  public DocumentUri Uri => TextDocumentItem.Uri;
  public int? Version => TextDocumentItem.Version;

  public IEnumerable<Diagnostic> Diagnostics =>
    ResolutionDiagnostics.Concat(ImplementationIdToView.Values.Select(v => v.Diagnostics).SelectMany(x => x));
}
