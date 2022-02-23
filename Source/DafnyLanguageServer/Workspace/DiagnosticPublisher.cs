using Microsoft.Dafny.LanguageServer.Util;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Server;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
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
      PublishVerificationDiagnostics(document);

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

    public void PublishVerificationDiagnostics(DafnyDocument document) {
      // Document.GetDiagnostics() returns not only resolution errors, but previous verification errors
      var errors = document.Errors.GetDiagnostics(document.GetFilePath())
        .Where(x => x.Severity == DiagnosticSeverity.Error)
        .OrderBy(x => x.Range.Start.Line)
        .ToArray();
      languageServer.TextDocument.SendNotification(new VerificationDiagnosticsParams {
        Uri = document.Uri,
        Version = document.Version,
        Diagnostics = errors,
        DiagnosticsAreResolutionErrors = document.VerificationPass == null,
        LinesCount = Regex.Matches(document.Text.Text, "\r?\n").Count + 1,
        PerNodeDiagnostic = document.VerificationNodeDiagnostic.Children.ToArray()
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
