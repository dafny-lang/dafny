using Microsoft.Dafny.LanguageServer.Util;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Server;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;

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
      PublishGhostDiagnostics(document);
    }

    private void PublishDocumentDiagnostics(DafnyDocument document) {
      var diagnosticParameters = new PublishDiagnosticsParams {
        Uri = document.Uri,
        Version = document.Version,
        Diagnostics = GetDiagnostics(document).ToArray(),
      };
      languageServer.TextDocument.PublishDiagnostics(diagnosticParameters);
    }

    public void PublishVerificationDiagnostics(DafnyDocument document) {
      if (document.LoadCanceled) {
        // We leave the responsibility to shift the error locations to the LSP clients.
        // Therefore, we do not republish the errors when the document (re-)load was canceled.
        return;
      }
      // Document.GetDiagnostics() returns not only resolution errors, but previous verification errors
      var currentDiagnostics =
        document.Errors.GetDiagnostics(document.GetFilePath())
          .Where(x => x.Severity == DiagnosticSeverity.Error).ToList();
      var errors = currentDiagnostics
        .Concat(document.OldVerificationDiagnostics)
        .Where(x => x.Severity == DiagnosticSeverity.Error)
        .ToArray();
      var linesCount = Regex.Matches(document.Text.Text, "\r?\n").Count + 1;
      var verificationDiagnosticsParams = new VerificationDiagnosticsParams(
        document.Uri,
        document.Version,
        document.VerificationNodeDiagnostic.Children.Select(child => child.GetCopyForNotification()).ToArray(),
        errors,
        linesCount,
        document.VerificationPass != null,
        document.ResolutionSucceeded == false ? currentDiagnostics.Count() : 0
      );
      languageServer.TextDocument.SendNotification(verificationDiagnosticsParams);
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
