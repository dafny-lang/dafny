using Microsoft.Dafny;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Server;
using System.Collections.Generic;
using System.Linq;
using System.Threading;

namespace DafnyLS.Language {
  internal class DiagnosticPublisher : IDiagnosticPublisher {
    private readonly ILanguageServer _languageServer;

    public DiagnosticPublisher(ILanguageServer languageServer) {
      _languageServer = languageServer;
    }

    public void PublishDiagnostics(DafnyDocument document, CancellationToken cancellationToken) {
      _languageServer.PublishDiagnostics(ToPublishDiagnostics(document, cancellationToken));
    }

    private static PublishDiagnosticsParams ToPublishDiagnostics(DafnyDocument document, CancellationToken cancellationToken) {
      return new PublishDiagnosticsParams {
        Uri = document.Uri,
        Version = document.Version,
        Diagnostics = ToDiagnostics(document.Errors, cancellationToken).ToArray(),
      };
    }

    private static IEnumerable<Diagnostic> ToDiagnostics(ErrorReporter errors, CancellationToken cancellationToken) {
      foreach(var (level, messages) in errors.AllMessages) {
        foreach(var message in messages) {
          cancellationToken.ThrowIfCancellationRequested();
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
