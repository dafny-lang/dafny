using System.Collections.Concurrent;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Server;
using System.Linq;
using OmniSharp.Extensions.LanguageServer.Protocol;

namespace Microsoft.Dafny.LanguageServer.Workspace {

  public class DiagnosticPublisher : IDiagnosticPublisher { // TODO rename to NotificationPublisher
    private readonly ILanguageServerFacade languageServer;

    public DiagnosticPublisher(ILanguageServerFacade languageServer) {
      this.languageServer = languageServer;
    }

    private readonly ConcurrentDictionary<DocumentUri, PublishDiagnosticsParams> previouslyPublishedDiagnostics = new();
    private readonly ConcurrentDictionary<DocumentUri, GhostDiagnosticsParams> previouslyPublishedGhostDiagnostics = new();

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
      if (previouslyPublishedDiagnostics.TryGetValue(document.Uri, out var previousParams) && previousParams.Diagnostics.SequenceEqual(diagnosticParameters.Diagnostics)) {
        return;
      }

      previouslyPublishedDiagnostics[document.Uri] = diagnosticParameters;
      languageServer.TextDocument.PublishDiagnostics(diagnosticParameters);
    }

    public void PublishVerificationDiagnostics(DafnyDocument document, bool verificationStarted) {
      if (document.LoadCanceled) {
        // We leave the responsibility to shift the error locations to the LSP clients.
        // Therefore, we do not republish the errors when the document (re-)load was canceled.
        return;
      }
      var errors = document.ParseAndResolutionDiagnostics.Where(x => x.Severity == DiagnosticSeverity.Error).ToList();
      var linesCount = document.LinesCount;
      var verificationStatusGutter = VerificationStatusGutter.ComputeFrom(
        document.Uri,
        document.Version,
        document.VerificationTree.Children.Select(child => child.GetCopyForNotification()).ToArray(),
        errors,
        linesCount,
        verificationStarted
      );
      languageServer.TextDocument.SendNotification(verificationStatusGutter);
    }

    private void PublishGhostDiagnostics(DafnyDocument document) {

      var newParams = new GhostDiagnosticsParams {
        Uri = document.Uri,
        Version = document.Version,
        Diagnostics = document.GhostDiagnostics.ToArray(),
      };
      if (previouslyPublishedGhostDiagnostics.TryGetValue(document.Uri, out var previousParams) && previousParams.Diagnostics.SequenceEqual(newParams.Diagnostics)) {
        return;
      }
      previouslyPublishedGhostDiagnostics[document.Uri] = newParams;
      languageServer.TextDocument.SendNotification(newParams);
    }

    public void HideDiagnostics(TextDocumentIdentifier documentId) {
      languageServer.TextDocument.PublishDiagnostics(new PublishDiagnosticsParams {
        Uri = documentId.Uri,
        Diagnostics = new Container<Diagnostic>()
      });
    }
  }
}