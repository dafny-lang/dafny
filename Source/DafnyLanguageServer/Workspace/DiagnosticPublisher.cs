using Microsoft.Dafny.LanguageServer.Util;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Server;
using System.Linq;

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
        Diagnostics = document.Diagnostics.ToArray(),
      };
      languageServer.TextDocument.PublishDiagnostics(diagnosticParameters);
    }

    public void PublishVerificationDiagnostics(DafnyDocument document, bool verificationStarted) {
      if (document.LoadCanceled) {
        // We leave the responsibility to shift the error locations to the LSP clients.
        // Therefore, we do not republish the errors when the document (re-)load was canceled.
        return;
      }
      var errors = document.Diagnostics.Where(x => x.Severity == DiagnosticSeverity.Error).ToList();
      var linesCount = document.LinesCount;
      var verificationStatusGutter = new VerificationStatusGutter(
        document.Uri,
        document.Version,
        document.VerificationTree.Children.Select(child => child.GetCopyForNotification()).ToArray(),
        errors,
        linesCount,
        verificationStarted,
        document.ParseAndResolutionDiagnostics.Count
      );
      languageServer.TextDocument.SendNotification(verificationStatusGutter);
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
  }
}
