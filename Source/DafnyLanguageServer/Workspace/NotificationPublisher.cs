using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Collections.Immutable;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Server;
using System.Linq;
using System.Net.Mime;
using Microsoft.Extensions.Logging;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Extensions.Options;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  public class NotificationPublisher : INotificationPublisher {
    private readonly ILogger<NotificationPublisher> logger;
    private readonly ILanguageServerFacade languageServer;
    private readonly VerifierOptions verifierOptions;

    public NotificationPublisher(ILogger<NotificationPublisher> logger, ILanguageServerFacade languageServer, IOptions<VerifierOptions> verifierOptions) {
      this.logger = logger;
      this.languageServer = languageServer;
      this.verifierOptions = verifierOptions.Value;
    }

    public void PublishNotifications(DocumentSnapshot previous, DocumentSnapshot document) {
      PublishVerificationStatus(previous, document);
      PublishDocumentDiagnostics(previous, document);
      PublishGhostDiagnostics(previous, document);
    }

    private void PublishVerificationStatus(DocumentSnapshot previousDocument, DocumentSnapshot document) {
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

    private static FileVerificationStatus? GetFileVerificationStatus(DocumentSnapshot document) {
      if (!document.ImplementationsWereUpdated) {
        /*
         CompilationAfterResolution.Snapshot() gets migrated ImplementationViews.
         It has to get migrated Diagnostics inside ImplementationViews, otherwise we get incorrect diagnostics.
         However, migrating the ImplementationId's may mean we lose verifiable symbols, which we don't want at this point. TODO: why not?
         To prevent publishing file verification status unless the current document has been translated,
         the field ImplementationsWereUpdated was added.
         */
        return null;
      }
      return new FileVerificationStatus(document.TextDocumentItem.Uri, document.TextDocumentItem.Version,
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

    private void PublishDocumentDiagnostics(DocumentSnapshot previousDocument, DocumentSnapshot document) {
      var diagnosticParameters = GetPublishDiagnosticsParams(document);
      var previousParams = GetPublishDiagnosticsParams(previousDocument);
      if (previousParams.Version > diagnosticParameters.Version ||
          previousParams.Diagnostics.SequenceEqual(diagnosticParameters.Diagnostics)) {
        return;
      }
      languageServer.TextDocument.PublishDiagnostics(diagnosticParameters);
    }

    private static PublishDiagnosticsParams GetPublishDiagnosticsParams(DocumentSnapshot document) {
      return new PublishDiagnosticsParams {
        Uri = document.TextDocumentItem.Uri,
        Version = document.TextDocumentItem.Version,
        Diagnostics = document.Diagnostics.ToArray(),
      };
    }

    public void PublishGutterIcons(DocumentSnapshot document, bool verificationStarted) {
      if (!verifierOptions.GutterStatus) {
        return;
      }

      var errors = document.ResolutionDiagnostics.Where(x => x.Severity == DiagnosticSeverity.Error).ToList();
      var linesCount = document.TextDocumentItem.NumberOfLines;
      var verificationStatusGutter = VerificationStatusGutter.ComputeFrom(
        document.Uri,
        document.TextDocumentItem.Version!.Value,
        document.VerificationTree.Children.Select(child => child.GetCopyForNotification()).ToArray(),
        errors,
        linesCount,
        verificationStarted
      );
      languageServer.TextDocument.SendNotification(verificationStatusGutter);
    }

    private void PublishGhostDiagnostics(DocumentSnapshot previousDocument, DocumentSnapshot document) {

      var newParams = GetGhostness(document);
      var previousParams = GetGhostness(previousDocument);
      if (previousParams.Diagnostics.SequenceEqual(newParams.Diagnostics)) {
        return;
      }
      languageServer.TextDocument.SendNotification(newParams);
    }

    private static GhostDiagnosticsParams GetGhostness(DocumentSnapshot document) {
      return new GhostDiagnosticsParams {
        Uri = document.TextDocumentItem.Uri,
        Version = document.TextDocumentItem.Version,
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
