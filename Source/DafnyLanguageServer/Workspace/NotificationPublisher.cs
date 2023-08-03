
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
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

    public void PublishNotifications(IdeState previousState, IdeState state) {
      if (state.Version < previousState.Version) {
        return;
      }

      PublishVerificationStatus(previousState, state);
      var _ = PublishDiagnostics(state);
      PublishGhostness(previousState, state);
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
      return state.ImplementationViews.GroupBy(kv => kv.Key.Uri).
        ToDictionary(kv => kv.Key.ToUri(), kvs =>
        new FileVerificationStatus(kvs.Key, state.Compilation.Version,
          kvs.SelectMany(kv => GetNamedVerifiableStatuses(kv.Key, kv.Value.Values)).
            OrderBy(s => s.NameRange.Start).ToList()));
    }

    private static List<NamedVerifiableStatus> GetNamedVerifiableStatuses(Location canVerify, ICollection<IdeImplementationView> implementationViews) {
      if (!implementationViews.Any()) {
        return new List<NamedVerifiableStatus>()
          { new(canVerify.Range, PublishedVerificationStatus.Stale) };
      }
      var namedVerifiableGroups = implementationViews.GroupBy(task => task.Range);
      return namedVerifiableGroups.Select(taskGroup => {
        var status = taskGroup.Select(kv => kv.Status).Aggregate(Combine);
        return new NamedVerifiableStatus(taskGroup.Key, status);
      }).OrderBy(v => v.NameRange.Start).ToList();
    }

    static PublishedVerificationStatus Combine(PublishedVerificationStatus first, PublishedVerificationStatus second) {
      return new[] { first, second }.Min();
    }

    private Dictionary<Uri, IList<Diagnostic>> publishedDiagnostics = new();

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
        } else {
          Console.Write("");
        }
      }
    }

    class RelatedInformationComparer : IEqualityComparer<DiagnosticRelatedInformation> {
      public bool Equals(DiagnosticRelatedInformation x, DiagnosticRelatedInformation y) {
        if (ReferenceEquals(x, y)) {
          return true;
        }

        if (ReferenceEquals(x, null)) {
          return false;
        }

        if (ReferenceEquals(y, null)) {
          return false;
        }

        if (x.GetType() != y.GetType()) {
          return false;
        }

        return x.Location.Equals(y.Location) && x.Message == y.Message;
      }

      public int GetHashCode(DiagnosticRelatedInformation obj) {
        return HashCode.Combine(obj.Location, obj.Message);
      }
    }

    class DiagnosticComparer : IEqualityComparer<Diagnostic> {
      private readonly RelatedInformationComparer relatedInformationComparer = new();
      public bool Equals(Diagnostic x, Diagnostic y) {
        if (ReferenceEquals(x, y)) {
          return true;
        }

        if (ReferenceEquals(x, null)) {
          return false;
        }

        if (ReferenceEquals(y, null)) {
          return false;
        }

        if (x.GetType() != y.GetType()) {
          return false;
        }

        if (ReferenceEquals(x.RelatedInformation, null) != ReferenceEquals(y.RelatedInformation, null)) {
          return false;
        }

        return x.Range.Equals(y.Range) && x.Severity == y.Severity && Nullable.Equals(x.Code, y.Code) &&
               Equals(x.CodeDescription, y.CodeDescription) &&
               x.Source == y.Source && x.Message == y.Message &&
               Equals(x.Tags, y.Tags) &&
               (ReferenceEquals(x.RelatedInformation, null) || x.RelatedInformation!.SequenceEqual(y.RelatedInformation!, relatedInformationComparer)) &&
               Equals(x.Data, y.Data);
      }

      public int GetHashCode(Diagnostic obj) {
        var hashCode = new HashCode();
        hashCode.Add(obj.Range);
        hashCode.Add(obj.Severity);
        hashCode.Add(obj.Code);
        hashCode.Add(obj.CodeDescription);
        hashCode.Add(obj.Source);
        hashCode.Add(obj.Message);
        hashCode.Add(obj.Tags);
        foreach (var info in obj.RelatedInformation ?? Enumerable.Empty<DiagnosticRelatedInformation>()) {
          hashCode.Add(relatedInformationComparer.GetHashCode(info));
        }
        hashCode.Add(obj.Data);
        return hashCode.ToHashCode();
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
      var verificationStatusGutter = VerificationStatusGutter.ComputeFrom(
        DocumentUri.From(uri),
        filesystem.GetVersion(uri) ?? 0,
        tree.Children.Select(child => child.GetCopyForNotification()).ToArray(),
        errors,
        linesCount,
        verificationStarted
      );

      lock (previouslyPublishedIcons) {
        var previous = previouslyPublishedIcons.GetValueOrDefault(uri);
        if (previous == null || !previous.PerLineStatus.SequenceEqual(verificationStatusGutter.PerLineStatus)) {
          previouslyPublishedIcons[uri] = verificationStatusGutter;
          languageServer.TextDocument.SendNotification(verificationStatusGutter);
        }
      }
    }

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
