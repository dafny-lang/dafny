
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

      await PublishDiagnostics(state);
      PublishProgress(previousState, state);
      PublishGhostness(previousState, state);
    }

    private void PublishProgress(IdeState previousState, IdeState state) {
      // Some global progress values, such as ResolutionSucceeded, will trigger the symbol progress to be displayed.
      // To ensure that the displayed progress is always up-to-date,
      // we must publish symbol progress before publishing the global one.

      // Better would be to have a single notification API with the schema { globalProgress, symbolProgress }
      // so this problem can not occur, although that would require the "symbolProgress" part to be able to contain a
      // "no-update" value to prevent having to send many duplicate symbolProgress updates.

      PublishSymbolProgress(previousState, state);
      PublishGlobalProgress(previousState, state);
    }

    private void PublishSymbolProgress(IdeState previousState, IdeState state) {
      foreach (var uri in state.Compilation.RootUris) {
        var previous = GetFileVerificationStatus(previousState, uri);
        var current = GetFileVerificationStatus(state, uri);

        if (Equals(current, previous)) {
          continue;
        }

        languageServer.TextDocument.SendNotification(DafnyRequestNames.VerificationSymbolStatus, current);
      }
    }

    private void PublishGlobalProgress(IdeState previousState, IdeState state) {
      foreach (var uri in state.Compilation.RootUris) {
        // TODO, still have to check for ownedness

        var current = GetGlobalProgress(state);
        var previous = GetGlobalProgress(previousState);

        if (Equals(current, previous)) {
          continue;
        }

        languageServer.SendNotification(new CompilationStatusParams {
          Uri = uri,
          Version = filesystem.GetVersion(uri),
          Status = current,
          Message = null
        });
      }

    }

    private CompilationStatus GetGlobalProgress(IdeState state) {
      var errors = state.ResolutionDiagnostics.Values.SelectMany(x => x).
        Where(d => d.Severity == DiagnosticSeverity.Error).ToList();
      if (state.Compilation is CompilationAfterResolution) {
        if (errors.Any(d => d.Source == MessageSource.Resolver.ToString())) {
          return CompilationStatus.ResolutionFailed;
        }

        return CompilationStatus.ResolutionSucceeded;
      }

      if (state.Compilation is CompilationAfterParsing) {
        if (errors.Any(d => d.Source == MessageSource.Parser.ToString())) {
          return CompilationStatus.ParsingFailed;
        }

        return CompilationStatus.ResolutionStarted;
      }

      return CompilationStatus.Parsing;
    }

    private FileVerificationStatus GetFileVerificationStatus(IdeState state, Uri uri) {
      var verificationResults = state.GetVerificationResults(uri);
      return new FileVerificationStatus(uri, filesystem.GetVersion(uri),
        verificationResults.Select(kv => GetNamedVerifiableStatuses(kv.Key, kv.Value)).
            OrderBy(s => s.NameRange.Start).ToList());
    }

    private static NamedVerifiableStatus GetNamedVerifiableStatuses(Range canVerify, IdeVerificationResult result) {
      var status = result.PreparationProgress switch {
        VerificationPreparationState.NotStarted => PublishedVerificationStatus.Stale,
        VerificationPreparationState.InProgress => PublishedVerificationStatus.Queued,
        VerificationPreparationState.Done =>
            new[] { PublishedVerificationStatus.Correct }. // If there is nothing to verify, show correct
              Concat(result.Implementations.Values.Select(v => v.Status)).Min(),
        _ => throw new ArgumentOutOfRangeException()
      };

      return new(canVerify, status);
    }

    private readonly Dictionary<Uri, IList<Diagnostic>> publishedDiagnostics = new();

    private async Task PublishDiagnostics(IdeState state) {
      // All root uris are added because we may have to publish empty diagnostics for owned uris.
      var sources = state.GetDiagnosticUris().Concat(state.Compilation.RootUris).Distinct();

      var projectDiagnostics = new List<Diagnostic>();
      foreach (var uri in sources) {
        var current = state.GetDiagnosticsForUri(uri);
        var uriProject = await projectManagerDatabase.GetProject(uri);
        var ownedUri = uriProject.Equals(state.Compilation.Project);
        if (ownedUri) {
          if (uri == state.Compilation.Project.Uri) {
            // Delay publication of project diagnostics,
            // since it also serves as a bucket for diagnostics from unowned files
            projectDiagnostics.AddRange(current);
          } else {
            PublishForUri(uri, current.ToArray());
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
            Version = filesystem.GetVersion(publishUri),
            Diagnostics = diagnostics,
          });
        }
      }
    }


    private readonly Dictionary<Uri, VerificationStatusGutter> previouslyPublishedIcons = new();
    public void PublishGutterIcons(Uri uri, IdeState state, bool verificationStarted) {
      if (!options.Get(GutterIconAndHoverVerificationDetailsManager.LineVerificationStatus)) {
        return;
      }

      var errors = state.ResolutionDiagnostics.GetOrDefault(uri, Enumerable.Empty<Diagnostic>).
        Where(x => x.Severity == DiagnosticSeverity.Error).ToList();
      var tree = state.VerificationTrees[uri];

      var linesCount = tree.Range.End.Line + 1;
      var fileVersion = filesystem.GetVersion(uri);
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
      { LineVerificationStatus.ResolutionError, @"/!\" },
      { LineVerificationStatus.Skipped, @" ? " }
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
