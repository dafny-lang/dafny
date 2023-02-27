using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
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

static class Util {
  public static Diagnostic ToLspDiagnostic(this DafnyDiagnostic dafnyDiagnostic) {
    return new Diagnostic {
      Code = dafnyDiagnostic.ErrorId,
      Severity = ToSeverity(dafnyDiagnostic.Level),
      Message = dafnyDiagnostic.Message,
      Range = dafnyDiagnostic.Token.GetLspRange(),
      Source = dafnyDiagnostic.Source.ToString(),
      RelatedInformation = relatedInformation,
      CodeDescription = dafnyDiagnostic.ErrorId == null
        ? null
        : new CodeDescription {Href = new Uri("https://dafny.org/dafny/HowToFAQ/Errors#" + dafnyDiagnostic.ErrorId)},
    };
  }

  private static DiagnosticSeverity ToSeverity(ErrorLevel level) {
    return level switch {
      ErrorLevel.Error => DiagnosticSeverity.Error,
      ErrorLevel.Warning => DiagnosticSeverity.Warning,
      ErrorLevel.Info => DiagnosticSeverity.Hint,
      _ => throw new ArgumentException($"unknown error level {level}", nameof(level))
    };
  }
}
