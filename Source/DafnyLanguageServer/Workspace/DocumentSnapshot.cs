using System.Collections.Generic;
using System.Linq;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public record DocumentSnapshot(
  DocumentTextBuffer TextDocumentItem,
  IEnumerable<Diagnostic> ResolutionDiagnostics,
  SymbolTable SymbolTable,
  IReadOnlyDictionary<ImplementationId, ImplementationView> ImplementationIdToView,
  bool ImplementationsWereUpdated,
  IEnumerable<Diagnostic> GhostDiagnostics,
  VerificationTree VerificationTree
) {

  public DocumentUri Uri => TextDocumentItem.Uri;
  public int? Version => TextDocumentItem.Version;

  public IEnumerable<Diagnostic> Diagnostics =>
    ResolutionDiagnostics.Concat(ImplementationIdToView.Values.Select(v => v.Diagnostics).SelectMany(x => x));
}
