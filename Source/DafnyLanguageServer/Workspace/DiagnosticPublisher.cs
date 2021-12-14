using Microsoft.Dafny.LanguageServer.Util;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Server;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  public class DiagnosticPublisher : IDiagnosticPublisher {
    private readonly ILanguageServerFacade languageServer;

    public DiagnosticPublisher(ILanguageServerFacade languageServer) {
      this.languageServer = languageServer;
    }

    public void PublishDiagnostics(DafnyDocument document) {
      if (document.LoadCanceled) {
        // We leave the responsibility to shift the error locations to the LSP clients.
        // Therefore, we do not republish the errors when the document (re-)load was canceled.
        return;
      }
      PublishDocumentDiagnostics(document);
      if (document.VerificationPass != null) {
        PublishVerificationDiagnostics(document);
      }

      PublishGhostDiagnostics(document);
    }

    private void PublishDocumentDiagnostics(DafnyDocument document) {
      var diagnosticParameterss = new PublishDiagnosticsParams {
        Uri = document.Uri,
        Version = document.Version,
        Diagnostics = GetDiagnostics(document).ToArray(),
      };
      languageServer.TextDocument.PublishDiagnostics(diagnosticParameterss);
    }

    // TODO: Write in Dafny
    private bool NoErrorWithin(IToken startTok, IToken endTok, Diagnostic[] errors) {
      // Errors are in order, we could just bissect them.
      for (var i = 0; i < errors.Length; i++) {
        var error = errors[i];
        if (startTok.line <= error.Range.End.Line && error.Range.Start.Line <= endTok.line) {
          return false;
        }
      }

      return true;
    }

    private void PublishVerificationDiagnostics(DafnyDocument document) {
      var errors = GetDiagnostics(document)
        .Where(x => x.Severity == DiagnosticSeverity.Error)
        .OrderBy(x => x.Range.Start.Line)
        .ToArray();
      var verified = new List<Range>();
      var unverified = new List<Range>();
      // Publish a green icon for every line of verified method if it does not contain any error
      foreach (var module in document.Program.Modules()) {
        foreach (var definition in module.TopLevelDecls) {
          if (definition is ClassDecl classDecl) {
            foreach (var member in classDecl.Members) {
              var range = new Range(
                member.tok.line - 1,
                member.tok.col,
                member.BodyEndTok.line - 1,
                member.BodyEndTok.col);
              if (NoErrorWithin(member.tok, member.BodyEndTok, errors)) {
                verified.Add(range);
              } else {
                unverified.Add(range);
              }
            }
          }
        }
      }
      languageServer.TextDocument.SendNotification(new VerificationDiagnosticsParams {
        Uri = document.Uri,
        Version = document.Version,
        Diagnostics = errors,
        Verified = verified.OrderBy(x => x.Start.Line).ToArray(),
        Unverified = unverified.OrderBy(x => x.Start.Line).ToArray()
      });
    }

    private void PublishGhostDiagnostics(DafnyDocument document) {
      languageServer.TextDocument.SendNotification(new GhostDiagnosticsParams {
        Uri = document.Uri,
        Version = document.Version,
        Diagnostics = document.GhostDiagnostics.ToArray(),
      });
    }

    public void HideDiagnostics(TextDocumentIdentifier documentId) {
      languageServer.TextDocument.PublishDiagnostics(new PublishDiagnosticsParams {
        Uri = documentId.Uri,
        Diagnostics = new Container<Diagnostic>()
      });
    }

    private static IEnumerable<Diagnostic> GetDiagnostics(DafnyDocument document) {
      // Only report errors of the entry-document.
      return document.Errors.GetDiagnostics(document.GetFilePath()).Concat(document.OldVerificationDiagnostics);
    }
  }
}
