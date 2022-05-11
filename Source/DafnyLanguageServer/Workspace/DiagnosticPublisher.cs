using System;
using System.Collections.Concurrent;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Server;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using OmniSharp.Extensions.LanguageServer.Protocol;
using VC;

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

    PublishedVerificationStatus FromImplementationTask(IImplementationTask task) {
      switch (task.CurrentStatus) {
        case VerificationStatus.Stale: return PublishedVerificationStatus.Stale;
        case VerificationStatus.Queued:
          return PublishedVerificationStatus.Queued;
        case VerificationStatus.Running:
          return PublishedVerificationStatus.Running;
        case VerificationStatus.Completed:
#pragma warning disable VSTHRD002
          return task.ActualTask.Result.Outcome == ConditionGeneration.Outcome.Correct
#pragma warning restore VSTHRD002
            ? PublishedVerificationStatus.Correct
            : PublishedVerificationStatus.Error;
        default:
          throw new ArgumentOutOfRangeException();
      }
    }

    static PublishedVerificationStatus Combine(PublishedVerificationStatus first, PublishedVerificationStatus second) {
      if (first == PublishedVerificationStatus.Error || second == PublishedVerificationStatus.Error) {
        return PublishedVerificationStatus.Error;
      }

      return new[] { first, second }.Min();
    }

    private void PublishVerificationStatus(DafnyDocument document) {
      var namedVerifiableGroups = document.VerificationTasks.GroupBy(task => task.Implementation.tok.GetLspRange());
      var namedVerifiableStatusList = namedVerifiableGroups.Select(taskGroup => {
        var statuses = taskGroup.Select(FromImplementationTask);
        var status = statuses.Aggregate(Combine);
        return new NamedVerifiableStatus(taskGroup.Key, status);
      }).ToList();
      var notification = new FileVerificationStatus(document.Uri, document.Version, namedVerifiableStatusList);

      if (previouslyVerificationStatus.TryGetValue(document.Uri, out var previous) && previous.Equals(notification)) {
        Console.Write("");
      } else {
        languageServer.TextDocument.SendNotification(VerificationStatusNotification, notification);
        previouslyVerificationStatus.AddOrUpdate(document.Uri, _ => notification, (_, _) => notification);
      }
    }

    private void PublishDocumentDiagnostics(DafnyDocument document) {
      var newParams = new PublishDiagnosticsParams {
        Uri = document.Uri,
        Version = document.Version,
        Diagnostics = document.Diagnostics.ToArray(),
      };
      if (previouslyPublishedDiagnostics.TryGetValue(document.Uri, out var previousParams) && previousParams.Diagnostics.Equals(newParams.Diagnostics)) {
        return;
      }

      previouslyPublishedDiagnostics.AddOrUpdate(document.Uri, _ => newParams, (_, _) => newParams);
      languageServer.TextDocument.PublishDiagnostics(newParams);
    }

    private void PublishGhostDiagnostics(DafnyDocument document) {

      var newParams = new GhostDiagnosticsParams {
        Uri = document.Uri,
        Version = document.Version,
        Diagnostics = document.GhostDiagnostics.ToArray(),
      };
      if (previouslyPublishedGhostDiagnostics.TryGetValue(document.Uri, out var previousParams) && previousParams.Diagnostics.Equals(newParams.Diagnostics)) {
        return;
      }
      previouslyPublishedGhostDiagnostics.AddOrUpdate(document.Uri, _ => newParams, (_, _) => newParams);
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
