
using System;
using System.Collections.Generic;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Server;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  public class NotificationPublisher : INotificationPublisher {
    private readonly ILogger<NotificationPublisher> logger;
    private readonly LanguageServerFilesystem filesystem;
    private readonly ILanguageServerFacade languageServer;
    private readonly IProjectDatabase projectManagerDatabase;
    private readonly DafnyOptions options;

    public NotificationPublisher(ILogger<NotificationPublisher> logger, ILanguageServerFacade languageServer,
      IProjectDatabase projectManagerDatabase,
      DafnyOptions options, LanguageServerFilesystem filesystem) {
      this.logger = logger;
      this.languageServer = languageServer;
      this.projectManagerDatabase = projectManagerDatabase;
      this.options = options;
      this.filesystem = filesystem;
    }

    public async Task PublishNotifications(IdeState previousState, IdeState state) {
      if (state.Version < previousState.Version) {
        return;
      }

      PublishVerificationStatus(previousState, state);
      PublishGhostness(previousState, state);
      await PublishDiagnostics(state);
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
      return state.VerificationResults.GroupBy(kv => kv.Key.Uri).
        ToDictionary(kv => kv.Key.ToUri(), kvs =>
        new FileVerificationStatus(kvs.Key, state.Compilation.Version,
          kvs.Select(kv => GetNamedVerifiableStatuses(kv.Key, kv.Value)).
            OrderBy(s => s.NameRange.Start).ToList()));
    }

    private static NamedVerifiableStatus GetNamedVerifiableStatuses(Location canVerify, IdeVerificationResult result) {
      var status = result.WasTranslated
        ? result.Implementations.Any()
          ? result.Implementations.Values.Select(v => v.Status).Aggregate(Combine)
          : PublishedVerificationStatus.Correct
        : PublishedVerificationStatus.Stale;

      return new(canVerify.Range, status);
    }

    static PublishedVerificationStatus Combine(PublishedVerificationStatus first, PublishedVerificationStatus second) {
      return new[] { first, second }.Min();
    }

    private readonly Dictionary<Uri, IList<Diagnostic>> publishedDiagnostics = new();

    private async Task PublishDiagnostics(IdeState state) {
      var currentDiagnostics = state.GetDiagnostics();

      // All root uris are added because we may have to publish empty diagnostics for owned uris.
      var sources = currentDiagnostics.Keys.Concat(state.Compilation.RootUris).Distinct();

      var projectDiagnostics = new List<Diagnostic>();
      foreach (var uri in sources) {
        var current = currentDiagnostics.GetOrDefault(uri, Enumerable.Empty<Diagnostic>).ToArray();
        var uriProject = await projectManagerDatabase.GetProject(uri);
        var ownedUri = uriProject.Equals(state.Compilation.Project);
        if (ownedUri) {
          if (uri == state.Compilation.Project.Uri) {
            // Delay publication of project diagnostics,
            // since it also serves as a bucket for diagnostics from unowned files
            projectDiagnostics.AddRange(current);
          } else {
            PublishForUri(uri, currentDiagnostics.GetOrDefault(uri, Enumerable.Empty<Diagnostic>).ToArray());
          }
        } else {
          var errors = current.Where(d => d.Severity == DiagnosticSeverity.Error).ToList();
          if (!errors.Any()) {
            continue;
          }

          projectDiagnostics.Add(new Diagnostic {
            Range = new Range(0, 0, 0, 1),
            Message = $"the referenced file {uri.LocalPath} contains error(s) but is not owned by this project. The first error is:\n{errors.First().Message}",
            Severity = DiagnosticSeverity.Error,
            Source = MessageSource.Parser.ToString()
          });
        }
      }

      PublishForUri(state.Compilation.Project.Uri, projectDiagnostics.ToArray());

      void PublishForUri(Uri publishUri, Diagnostic[] diagnostics) {
        var previous = publishedDiagnostics.GetOrDefault(publishUri, Enumerable.Empty<Diagnostic>);
        if (!previous.SequenceEqual(diagnostics, new DiagnosticComparer())) {
          if (diagnostics.Any()) {
            publishedDiagnostics[publishUri] = diagnostics;
          } else {
            // Prevent memory leaks by cleaning up previous state when it's the IDE's initial state.
            publishedDiagnostics.Remove(publishUri);
          }

          languageServer.TextDocument.PublishDiagnostics(new PublishDiagnosticsParams {
            Uri = publishUri,
            Version = filesystem.GetVersion(publishUri) ?? 0,
            Diagnostics = diagnostics,
          });
        }
      }
    }


    private readonly Dictionary<Uri, VerificationStatusGutter> previouslyPublishedIcons = new();
    public void PublishGutterIcons(Uri uri, IdeState state, bool verificationStarted) {
      if (!options.Get(ServerCommand.LineVerificationStatus)) {
        return;
      }

      var errors = state.ResolutionDiagnostics.GetOrDefault(uri, Enumerable.Empty<Diagnostic>).
        Where(x => x.Severity == DiagnosticSeverity.Error).ToList();
      var tree = state.VerificationTrees[uri];

      var linesCount = tree.Range.End.Line + 1;
      var fileVersion = filesystem.GetVersion(uri) ?? 0;
      var verificationStatusGutter = VerificationStatusGutter.ComputeFrom(
        DocumentUri.From(uri),
        fileVersion,
        tree.Children,
        errors,
        linesCount,
        verificationStarted
      );
      if (logger.IsEnabled(LogLevel.Trace)) {
        var icons = string.Join(' ', verificationStatusGutter.PerLineStatus.Select(s => LineVerificationStatusToString[s]));
        logger.LogDebug($"Sending gutter icons for compilation {state.Compilation.Project.Uri}, comp version {state.Version}, file version {fileVersion}" +
                        $"icons: {icons}\n" +
                        $"stacktrace:\n{Environment.StackTrace}");
      };


      lock (previouslyPublishedIcons) {
        var previous = previouslyPublishedIcons.GetValueOrDefault(uri);
        if (previous == null || !previous.PerLineStatus.SequenceEqual(verificationStatusGutter.PerLineStatus)) {
          previouslyPublishedIcons[uri] = verificationStatusGutter;
          languageServer.TextDocument.SendNotification(verificationStatusGutter);
        }
      }
    }

    public static Dictionary<LineVerificationStatus, string> LineVerificationStatusToString = new() {
      { LineVerificationStatus.Nothing, "   " },
      { LineVerificationStatus.Scheduled, " . " },
      { LineVerificationStatus.Verifying, " S " },
      { LineVerificationStatus.VerifiedObsolete, " I " },
      { LineVerificationStatus.VerifiedVerifying, " $ " },
      { LineVerificationStatus.Verified, " | " },
      { LineVerificationStatus.ErrorContextObsolete, "[I]" },
      { LineVerificationStatus.ErrorContextVerifying, "[S]" },
      { LineVerificationStatus.ErrorContext, "[ ]" },
      { LineVerificationStatus.AssertionFailedObsolete, "[-]" },
      { LineVerificationStatus.AssertionFailedVerifying, "[~]" },
      { LineVerificationStatus.AssertionFailed, "[=]" },
      { LineVerificationStatus.AssertionVerifiedInErrorContextObsolete, "[o]" },
      { LineVerificationStatus.AssertionVerifiedInErrorContextVerifying, "[Q]" },
      { LineVerificationStatus.AssertionVerifiedInErrorContext, "[O]" },
      { LineVerificationStatus.ResolutionError, @"/!\" }
    };

    private void PublishGhostness(IdeState previousState, IdeState state) {

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
