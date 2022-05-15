using System.Collections.Concurrent;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Server;
using System.Linq;
using OmniSharp.Extensions.LanguageServer.Protocol;

namespace Microsoft.Dafny.LanguageServer.Workspace {

  public class DiagnosticPublisher : IDiagnosticPublisher { // TODO rename to NotificationPublisher
    public const string VerificationStatusNotification = "textDocument/verificationStatus";
    private readonly ILanguageServerFacade languageServer;

    public DiagnosticPublisher(ILanguageServerFacade languageServer) {
      this.languageServer = languageServer;
    }

    private readonly ConcurrentDictionary<DocumentUri, PublishDiagnosticsParams> previouslyPublishedDiagnostics = new();
    private readonly ConcurrentDictionary<DocumentUri, GhostDiagnosticsParams> previouslyPublishedGhostDiagnostics = new();
    private readonly ConcurrentDictionary<DocumentUri, FileVerificationStatus> previouslyVerificationStatus = new();

    public void PublishDiagnostics(DafnyDocument document) {
      if (document.LoadCanceled) {
        // We leave the responsibility to shift the error locations to the LSP clients.
        // Therefore, we do not republish the errors when the document (re-)load was canceled.
        return;
      }

      PublishVerificationStatus(document);
      PublishDocumentDiagnostics(document);
      PublishGhostDiagnostics(document);
    }

    private void PublishVerificationStatus(DafnyDocument document) {
      if (document.ImplementationViews == null) {
        return;
      }

      var namedVerifiableGroups = document.ImplementationViews.GroupBy(task => task.Value.Range);
      var namedVerifiableStatusList = namedVerifiableGroups.Select(taskGroup => {
        var status = taskGroup.Select(kv => kv.Value.Status).Aggregate(Combine);
        return new NamedVerifiableStatus(taskGroup.Key, status);
      }).OrderBy(v => v.NameRange.Start).ToList();
      var notification = new FileVerificationStatus(document.Uri, document.Version, namedVerifiableStatusList);

      if (!previouslyVerificationStatus.TryGetValue(document.Uri, out var previous) || !previous.Equals(notification)) {
        languageServer.TextDocument.SendNotification(VerificationStatusNotification, notification);
        previouslyVerificationStatus[document.Uri] = notification;
      }
    }

    static PublishedVerificationStatus Combine(PublishedVerificationStatus first, PublishedVerificationStatus second) {
      if (first == PublishedVerificationStatus.Error || second == PublishedVerificationStatus.Error) {
        return PublishedVerificationStatus.Error;
      }

      return new[] { first, second }.Min();
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

    public void PublishGutterIcons(DafnyDocument document, bool verificationStarted) {
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