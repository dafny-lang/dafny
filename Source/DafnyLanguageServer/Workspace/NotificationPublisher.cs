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
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Extensions.Options;
using OmniSharp.Extensions.LanguageServer.Protocol;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  public record CompilationView(
    DocumentTextBuffer TextDocumentItem,
    IEnumerable<Diagnostic> ResolutionDiagnostics,
    SymbolTable SymbolTable,
    IReadOnlyDictionary<ImplementationId, ImplementationView> ImplementationViews,
    bool ImplementationsWereUpdated,
    bool LoadCanceled,
    IEnumerable<Diagnostic> GhostDiagnostics,
    VerificationTree VerificationTree
    ) {

    public DocumentUri Uri => TextDocumentItem.Uri;
    public int? Version => TextDocumentItem.Version;
    
    public IEnumerable<Diagnostic> Diagnostics =>
      ResolutionDiagnostics.Concat(ImplementationViews.Values.Select(v => v.Diagnostics).SelectMany(x => x));
  }

  public class NotificationPublisher : INotificationPublisher {
    private readonly ILogger<NotificationPublisher> logger;
    private readonly ILanguageServerFacade languageServer;
    private readonly VerifierOptions verifierOptions;

    public NotificationPublisher(ILogger<NotificationPublisher> logger, ILanguageServerFacade languageServer, IOptions<VerifierOptions> verifierOptions) {
      this.logger = logger;
      this.languageServer = languageServer;
      this.verifierOptions = verifierOptions.Value;
    }

    public void PublishNotifications(CompilationView previous, CompilationView document) {
      if (document.LoadCanceled) {
        // We leave the responsibility to shift the error locations to the LSP clients.
        // Therefore, we do not republish the errors when the document (re-)load was canceled.
        return;
      }

      PublishVerificationStatus(previous, document);
      PublishDocumentDiagnostics(previous, document);
      PublishGhostDiagnostics(previous, document);
    }

    private void PublishVerificationStatus(CompilationView previousDocument, CompilationView document) {
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

    private static FileVerificationStatus? GetFileVerificationStatus(CompilationView document) {
      if (!document.ImplementationsWereUpdated) {
        return null;
      }
      return new FileVerificationStatus(document.TextDocumentItem.Uri, document.TextDocumentItem.Version,
        GetNamedVerifiableStatuses(document.ImplementationViews));
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

    private void PublishDocumentDiagnostics(CompilationView previousDocument, CompilationView document) {
      var diagnosticParameters = GetPublishDiagnosticsParams(document);
      var previousParams = GetPublishDiagnosticsParams(previousDocument);
      if (previousParams.Version > diagnosticParameters.Version ||
          previousParams.Diagnostics.SequenceEqual(diagnosticParameters.Diagnostics)) {
        return;
      }
      languageServer.TextDocument.PublishDiagnostics(diagnosticParameters);
    }

    private static PublishDiagnosticsParams GetPublishDiagnosticsParams(CompilationView document) {
      return new PublishDiagnosticsParams {
        Uri = document.TextDocumentItem.Uri,
        Version = document.TextDocumentItem.Version,
        Diagnostics = document.Diagnostics.ToArray(),
      };
    }

    public void PublishGutterIcons(CompilationView document, bool verificationStarted) {
      if (!verifierOptions.GutterStatus) {
        return;
      }

      if (document.LoadCanceled) {
        // We leave the responsibility to shift the error locations to the LSP clients.
        // Therefore, we do not republish the errors when the document (re-)load was canceled.
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

    private void PublishGhostDiagnostics(CompilationView previousDocument, CompilationView document) {

      var newParams = GetGhostness(document);
      var previousParams = GetGhostness(previousDocument);
      if (previousParams.Diagnostics.SequenceEqual(newParams.Diagnostics)) {
        return;
      }
      languageServer.TextDocument.SendNotification(newParams);
    }

    private static GhostDiagnosticsParams GetGhostness(CompilationView document) {
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
