using System;
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
    private readonly DafnyOptions options;

    public NotificationPublisher(ILogger<NotificationPublisher> logger, ILanguageServerFacade languageServer, DafnyOptions options) {
      this.logger = logger;
      this.languageServer = languageServer;
      this.options = options;
    }

    public void PublishNotifications(IdeState previousState, IdeState state) {
      PublishVerificationStatus(previousState, state);
      PublishDocumentDiagnostics(previousState, state);
      PublishGhostDiagnostics(previousState, state);
    }

    private void PublishVerificationStatus(IdeState previousState, IdeState state) {
      var notification = GetFileVerificationStatus(state);
      if (notification == null) {
        // Do not publish verification status while resolving
        return;
      }

      var previous = GetFileVerificationStatus(previousState);
      if (previous != null && (previous.Version > notification.Version ||
          previous.NamedVerifiables.SequenceEqual(notification.NamedVerifiables))) {
        return;
      }

      languageServer.TextDocument.SendNotification(DafnyRequestNames.VerificationSymbolStatus, notification);
    }

    private static FileVerificationStatus? GetFileVerificationStatus(IdeState state) {
      if (!state.ImplementationsWereUpdated) {
        /*
         DocumentAfterResolution.Snapshot() gets migrated ImplementationViews.
         It has to get migrated Diagnostics inside ImplementationViews, otherwise we get incorrect diagnostics.
         However, migrating the ImplementationId's may mean we lose verifiable symbols, which we don't want at this point. TODO: why not?
         To prevent publishing file verification status unless the current document has been translated,
         the field ImplementationsWereUpdated was added.
         */
        return null;
      }
      return new FileVerificationStatus(state.TextDocumentItem.Uri, state.TextDocumentItem.Version,
        GetNamedVerifiableStatuses(state.ImplementationIdToView));
    }

    private static List<NamedVerifiableStatus> GetNamedVerifiableStatuses(IReadOnlyDictionary<ImplementationId, IdeImplementationView> implementationViews) {
      var namedVerifiableGroups = implementationViews.GroupBy(task => task.Value.Range);
      return namedVerifiableGroups.Select(taskGroup => {
        var status = taskGroup.Select(kv => kv.Value.Status).Aggregate(Combine);
        return new NamedVerifiableStatus(taskGroup.Key, status);
      }).OrderBy(v => v.NameRange.Start).ToList();
    }

    static PublishedVerificationStatus Combine(PublishedVerificationStatus first, PublishedVerificationStatus second) {
      return new[] { first, second }.Min();
    }

    private void PublishDocumentDiagnostics(IdeState previousState, IdeState state) {
      var diagnosticParameters = GetPublishDiagnosticsParams(state);
      var previousParams = GetPublishDiagnosticsParams(previousState);
      if (previousParams.Version > diagnosticParameters.Version ||
          previousParams.Diagnostics.SequenceEqual(diagnosticParameters.Diagnostics)) {
        return;
      }
      languageServer.TextDocument.PublishDiagnostics(diagnosticParameters);
    }

    private static PublishDiagnosticsParams GetPublishDiagnosticsParams(IdeState state) {
      return new PublishDiagnosticsParams {
        Uri = state.TextDocumentItem.Uri,
        Version = state.TextDocumentItem.Version,
        Diagnostics = state.Diagnostics.ToArray(),
      };
    }

    public void PublishGutterIcons(IdeState state, bool verificationStarted) {
      if (!options.Get(ServerCommand.LineVerificationStatus)) {
        return;
      }

      var errors = state.ResolutionDiagnostics.Where(x => x.Severity == DiagnosticSeverity.Error).ToList();
      var linesCount = state.TextDocumentItem.NumberOfLines;
      var verificationStatusGutter = VerificationStatusGutter.ComputeFrom(
        state.Uri,
        state.TextDocumentItem.Version!.Value,
        state.VerificationTree.Children.Select(child => child.GetCopyForNotification()).ToArray(),
        errors,
        linesCount,
        verificationStarted
      );
      languageServer.TextDocument.SendNotification(verificationStatusGutter);
    }

    private void PublishGhostDiagnostics(IdeState previousState, IdeState state) {

      var newParams = GetGhostness(state);
      var previousParams = GetGhostness(previousState);
      if (previousParams.Diagnostics.SequenceEqual(newParams.Diagnostics)) {
        return;
      }
      languageServer.TextDocument.SendNotification(newParams);
    }

    private static GhostDiagnosticsParams GetGhostness(IdeState state) {

      return new GhostDiagnosticsParams {
        Uri = state.TextDocumentItem.Uri,
        Version = state.TextDocumentItem.Version,
        Diagnostics = state.GhostDiagnostics.ToArray(),
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
