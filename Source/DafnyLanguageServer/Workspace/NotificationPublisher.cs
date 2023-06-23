using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Server;
using System.Linq;
using Microsoft.Extensions.Logging;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  public class NotificationPublisher : INotificationPublisher {
    private readonly ILogger<NotificationPublisher> logger;
    private readonly LanguageServerFilesystem filesystem;
    private readonly ILanguageServerFacade languageServer;
    private readonly DafnyOptions options;

    public NotificationPublisher(ILogger<NotificationPublisher> logger, ILanguageServerFacade languageServer, 
      DafnyOptions options, LanguageServerFilesystem filesystem) {
      this.logger = logger;
      this.languageServer = languageServer;
      this.options = options;
      this.filesystem = filesystem;
    }

    public void PublishNotifications(IdeState previousState, IdeState state) {
      if (state.Version < previousState.Version) {
        return;
      }

      PublishVerificationStatus(previousState, state);
      PublishDocumentDiagnostics(previousState, state);
      PublishGhostDiagnostics(previousState, state);
    }

    private void PublishVerificationStatus(IdeState previousState, IdeState state) {
      var currentPerFile = GetFileVerificationStatus(state);
      var previousPerFile = GetFileVerificationStatus(previousState);
      foreach (var (uri, current) in currentPerFile) {
        if (previousPerFile.TryGetValue(uri, out var previous)) {
          if (previous.NamedVerifiables.SequenceEqual(current.NamedVerifiables)) {
            continue;
          }
        }
        languageServer.TextDocument.SendNotification(DafnyRequestNames.VerificationSymbolStatus, current);
      }
    }

    private static IDictionary<Uri, FileVerificationStatus> GetFileVerificationStatus(IdeState state) {
      if (!state.ImplementationsWereUpdated) {
        /*
         DocumentAfterResolution.Snapshot() gets migrated ImplementationViews.
         It has to get migrated Diagnostics inside ImplementationViews, otherwise we get incorrect diagnostics.
         However, migrating the ImplementationId's may mean we lose verifiable symbols, which we don't want at this point. TODO: why not?
         To prevent publishing file verification status unless the current document has been translated,
         the field ImplementationsWereUpdated was added.
         */
        return ImmutableDictionary<Uri, FileVerificationStatus>.Empty;
      }

      return state.ImplementationIdToView.GroupBy(kv => kv.Key.Uri).
        ToDictionary(kv => kv.Key, kv =>
        new FileVerificationStatus(kv.Key, null,
          GetNamedVerifiableStatuses(state.ImplementationIdToView)));
    }

    private static List<NamedVerifiableStatus> GetNamedVerifiableStatuses(IReadOnlyDictionary<ImplementationId, IdeImplementationView> implementationViews) {
      var namedVerifiableGroups = implementationViews.Values.GroupBy(task => task.Range);
      return namedVerifiableGroups.Select(taskGroup => {
        var status = taskGroup.Select(kv => kv.Status).Aggregate(Combine);
        return new NamedVerifiableStatus(taskGroup.Key, status);
      }).OrderBy(v => v.NameRange.Start).ToList();
    }

    static PublishedVerificationStatus Combine(PublishedVerificationStatus first, PublishedVerificationStatus second) {
      return new[] { first, second }.Min();
    }

    private void PublishDocumentDiagnostics(IdeState previousState, IdeState state) {
      var previousStateDiagnostics = previousState.GetDiagnostics();
      var currentDiagnostics = state.GetDiagnostics();
      var uris = previousStateDiagnostics.Keys.Concat(currentDiagnostics.Keys).Distinct();
      foreach (var uri in uris) {
        IEnumerable<Diagnostic> current = currentDiagnostics.GetOrDefault(uri, Enumerable.Empty<Diagnostic>);
        IEnumerable<Diagnostic> previous = previousStateDiagnostics.GetOrDefault(uri, Enumerable.Empty<Diagnostic>);
        if (previous.SequenceEqual(current)) {
          continue;
        }
        languageServer.TextDocument.PublishDiagnostics(new PublishDiagnosticsParams {
          Uri = uri,
          Version = filesystem.GetVersion(uri),
          Diagnostics = current.ToList(),
        });
      }
    }

    public void PublishGutterIcons(IdeState state, bool verificationStarted) {
      if (!options.Get(ServerCommand.LineVerificationStatus)) {
        return;
      }

      // var errors = state.ResolutionDiagnostics.Where(x => x.Severity == DiagnosticSeverity.Error).ToList();
      // var linesCount = 200; // TODO resolve. state.DocumentIdentifier.NumberOfLines;
      // var verificationStatusGutter = VerificationStatusGutter.ComputeFrom(
      //   state.Uri,
      //   state.DocumentIdentifier.Version,
      //   state.VerificationTree.Children.Select(child => child.GetCopyForNotification()).ToArray(),
      //   errors,
      //   linesCount,
      //   verificationStarted
      // );
      // languageServer.TextDocument.SendNotification(verificationStatusGutter);
    }

    private void PublishGhostDiagnostics(IdeState previousState, IdeState state) {

      var newParams = state.GhostRanges;
      var previousParams = state.GhostRanges;
      foreach (var (uri, current) in newParams) {
        if (previousParams.TryGetValue(uri, out var previous)) {
          if (previous.SequenceEqual(current)) {
            continue;
          }
        }
        languageServer.TextDocument.SendNotification(new GhostDiagnosticsParams {
          Uri = uri,
          Version = state.Version,
          Diagnostics = current.Select(r => new Diagnostic {
            Range = r
          }).ToArray(),
        });
      }
    }

    public void HideDiagnostics(TextDocumentIdentifier documentId) {
      languageServer.TextDocument.PublishDiagnostics(new PublishDiagnosticsParams {
        Uri = documentId.Uri,
        Diagnostics = new Container<Diagnostic>()
      });
    }
  }
}
