
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Server;
using System.Linq;
using Microsoft.Extensions.Logging;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

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
        ToDictionary(kv => kv.Key, kvs =>
        new FileVerificationStatus(kvs.Key, null,
          GetNamedVerifiableStatuses(kvs.Select(kv => kv.Value))));
    }

    private static List<NamedVerifiableStatus> GetNamedVerifiableStatuses(IEnumerable<IdeImplementationView> implementationViews) {
      var namedVerifiableGroups = implementationViews.GroupBy(task => task.Range);
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
      var singleFileDiagnostics = state.Compilation.Project.UnsavedRootFile;
      if (singleFileDiagnostics == null) {
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
      } else {
        var diagnostics = new List<Diagnostic>();
        foreach (var (key, value) in currentDiagnostics) {
          if (key == singleFileDiagnostics) {
            diagnostics.AddRange(value);
          } else {
            if (value.Any()) {
              var containsErrorSTheFirstOneIs =
                $"the referenced file {key.LocalPath} contains error(s). The first one is: {value.First().Message}";
              var diagnostic = new Diagnostic() {
                Range = new Range(0, 0, 0, 1),
                Message = containsErrorSTheFirstOneIs,
                Severity = DiagnosticSeverity.Error,
                Source = MessageSource.Parser.ToString()
              };
              diagnostics.Add(diagnostic);
            }
          }
        }
        IEnumerable<Diagnostic> previous = previousStateDiagnostics.GetOrDefault(singleFileDiagnostics, Enumerable.Empty<Diagnostic>);
        if (!previous.SequenceEqual(diagnostics)) {
          languageServer.TextDocument.PublishDiagnostics(new PublishDiagnosticsParams {
            Uri = singleFileDiagnostics,
            Version = filesystem.GetVersion(singleFileDiagnostics),
            Diagnostics = diagnostics,
          });
        }
      }
    }

    public void PublishGutterIcons(IdeState state, bool verificationStarted) {
      if (!options.Get(ServerCommand.LineVerificationStatus)) {
        return;
      }

      var root = state.Compilation.Project.UnsavedRootFile;
      if (root == null) {
        return;
      }
      var errors = state.ResolutionDiagnostics.GetOrDefault(root, Enumerable.Empty<Diagnostic>).
        Where(x => x.Severity == DiagnosticSeverity.Error).ToList();
      if (state.VerificationTree == null) {
        return;
      }

      var linesCount = state.VerificationTree.Range.End.Line + 1;
      var verificationStatusGutter = VerificationStatusGutter.ComputeFrom(
        root,
        filesystem.GetVersion(root)!.Value,
        state.VerificationTree.Children.Select(child => child.GetCopyForNotification()).ToArray(),
        errors,
        linesCount,
        verificationStarted
      );
      languageServer.TextDocument.SendNotification(verificationStatusGutter);
    }

    private void PublishGhostDiagnostics(IdeState previousState, IdeState state) {

      var newParams = state.GhostRanges;
      var previousParams = previousState.GhostRanges;
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
  }
}
