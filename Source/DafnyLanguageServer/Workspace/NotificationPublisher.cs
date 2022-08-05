using System;
using System.Collections.Generic;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Server;
using System.Linq;

namespace Microsoft.Dafny.LanguageServer.Workspace {

  public class NotificationPublisher : INotificationPublisher {
    private readonly ILanguageServerFacade languageServer;

    public NotificationPublisher(ILanguageServerFacade languageServer) {
      this.languageServer = languageServer;
    }

    public void PublishNotifications(DafnyDocument previous, DafnyDocument document) {
      if (document.LoadCanceled) {
        // We leave the responsibility to shift the error locations to the LSP clients.
        // Therefore, we do not republish the errors when the document (re-)load was canceled.
        return;
      }

      PublishVerificationStatus(previous, document);
      PublishDocumentDiagnostics(previous, document);
      PublishGhostDiagnostics(previous, document);
    }

    private void PublishVerificationStatus(DafnyDocument previousDocument, DafnyDocument document) {
      var notification = GetFileVerificationStatus(document);
      if (notification == null) {
        // Do not publish verification status while resolving
        return;
      }

      var previous = GetFileVerificationStatus(previousDocument);
      if (previous != null && (previous.Version > notification.Version ||
          previous.NamedVerifiables.SequenceEqual(notification.NamedVerifiables))) {
        return;
      }

      languageServer.TextDocument.SendNotification(DafnyRequestNames.VerificationSymbolStatus, notification);
    }

    private static FileVerificationStatus? GetFileVerificationStatus(DafnyDocument document) {
      if (document.ImplementationIdToView == null || document.VerificationTasks == null) {
        return null;
      }
      return new FileVerificationStatus(document.Uri, document.Version,
        GetNamedVerifiableStatuses(document.ImplementationIdToView));
    }

    private static List<NamedVerifiableStatus> GetNamedVerifiableStatuses(IReadOnlyDictionary<ImplementationId, ImplementationView> implementationViews) {
      var namedVerifiableGroups = implementationViews.GroupBy(task => task.Value.Range);
      return namedVerifiableGroups.Select(taskGroup => {
        var status = taskGroup.Select(kv => kv.Value.Status).Aggregate(Combine);
        return new NamedVerifiableStatus(taskGroup.Key, status);
      }).OrderBy(v => v.NameRange.Start).ToList();
    }

    static PublishedVerificationStatus Combine(PublishedVerificationStatus first, PublishedVerificationStatus second) {
      return new[] { first, second }.Min();
    }

    private void PublishDocumentDiagnostics(DafnyDocument previousDocument, DafnyDocument document) {
      var diagnosticParameters = GetPublishDiagnosticsParams(document);
      var previousParams = GetPublishDiagnosticsParams(previousDocument);
      if (previousParams.Version > diagnosticParameters.Version ||
          previousParams.Diagnostics.SequenceEqual(diagnosticParameters.Diagnostics)) {
        return;
      }
      languageServer.TextDocument.PublishDiagnostics(diagnosticParameters);
    }

    private static PublishDiagnosticsParams GetPublishDiagnosticsParams(DafnyDocument document) {
      return new PublishDiagnosticsParams {
        Uri = document.Uri,
        Version = document.Version,
        Diagnostics = document.Diagnostics.ToArray(),
      };
    }

    public void PublishGutterIcons(DafnyDocument document, bool verificationStarted) {
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

    private void PublishGhostDiagnostics(DafnyDocument previousDocument, DafnyDocument document) {

      var newParams = GetGhostness(document);
      var previousParams = GetGhostness(previousDocument);
      if (previousParams.Diagnostics.SequenceEqual(newParams.Diagnostics)) {
        return;
      }
      languageServer.TextDocument.SendNotification(newParams);
    }

    private static GhostDiagnosticsParams GetGhostness(DafnyDocument document) {
      return new GhostDiagnosticsParams {
        Uri = document.Uri,
        Version = document.Version,
        Diagnostics = document.GhostDiagnostics.ToArray(),
      };
    }

    public void HideDiagnostics(TextDocumentIdentifier documentId) {
      languageServer.TextDocument.PublishDiagnostics(new PublishDiagnosticsParams {
        Uri = documentId.Uri,
        Diagnostics = new Container<Diagnostic>()
      });
    }
  }
}