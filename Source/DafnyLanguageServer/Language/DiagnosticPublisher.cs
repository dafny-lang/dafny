using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Server;
using System.Collections.Generic;
using System.Linq;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Language {
  public class DiagnosticPublisher : IDiagnosticPublisher {
    private readonly ILanguageServerFacade _languageServer;

    public DiagnosticPublisher(ILanguageServerFacade languageServer) {
      _languageServer = languageServer;
    }

    public void PublishDiagnostics(DafnyDocument document, CancellationToken cancellationToken) {
      _languageServer.TextDocument.PublishDiagnostics(ToPublishDiagnostics(document, cancellationToken));
    }

    public void HideDiagnostics(DafnyDocument document) {
      _languageServer.TextDocument.PublishDiagnostics(new PublishDiagnosticsParams {
        Uri = document.Uri,
        Version = document.Version,
        Diagnostics = new Container<Diagnostic>()
      });
    }

    private static PublishDiagnosticsParams ToPublishDiagnostics(DafnyDocument document, CancellationToken cancellationToken) {
      return new PublishDiagnosticsParams {
        Uri = document.Uri,
        Version = document.Version,
        Diagnostics = ToDiagnostics(document, cancellationToken).ToArray(),
      };
    }

    private static IEnumerable<Diagnostic> ToDiagnostics(DafnyDocument document, CancellationToken cancellationToken) {
      foreach(var (level, messages) in document.Errors.AllMessages) {
        foreach(var message in messages) {
          cancellationToken.ThrowIfCancellationRequested();
          if(!document.IsPartOf(message.token)) {
            // TODO The reported error belongs to another file. Report it anyway?
            continue;
          }
          yield return new Diagnostic {
            Severity = ToSeverity(level),
            Range = message.token.GetLspRange(),
            Message = message.message,
            Source = message.source.ToString()
          };
        }
      }
    }

    private static DiagnosticSeverity ToSeverity(ErrorLevel level) {
      return level switch {
        ErrorLevel.Error => DiagnosticSeverity.Error,
        ErrorLevel.Warning => DiagnosticSeverity.Warning,
        ErrorLevel.Info => DiagnosticSeverity.Information,
        _ => throw new System.ArgumentException($"unknown error level {level}", nameof(level))
      };
    }
  }
}
