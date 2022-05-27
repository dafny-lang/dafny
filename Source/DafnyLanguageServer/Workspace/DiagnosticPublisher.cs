using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Collections.Immutable;
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

      var notification = new FileVerificationStatus(document.Uri, document.Version, GetNamedVerifiableStatuses(document.ImplementationViews));

      if (previouslyVerificationStatus.TryGetValue(document.Uri, out var previousParams)) {
        if (previousParams.Version > notification.Version ||
            previousParams.NamedVerifiables.SequenceEqual(notification.NamedVerifiables)) {
          return;
        }
      } else {
        if (!notification.NamedVerifiables.Any()) {
          return;
        }
      }

      languageServer.TextDocument.SendNotification(DafnyRequestNames.VerificationSymbolStatus, notification);
      previouslyVerificationStatus[document.Uri] = notification;
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

    private void PublishDocumentDiagnostics(DafnyDocument document) {
      var diagnosticParameters = new PublishDiagnosticsParams {
        Uri = document.Uri,
        Version = document.Version,
        Diagnostics = document.Diagnostics.ToArray(),
      };
      if (previouslyPublishedDiagnostics.TryGetValue(document.Uri, out var previousParams) &&
          (previousParams.Version > diagnosticParameters.Version ||
           previousParams.Diagnostics.SequenceEqual(diagnosticParameters.Diagnostics))) {
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