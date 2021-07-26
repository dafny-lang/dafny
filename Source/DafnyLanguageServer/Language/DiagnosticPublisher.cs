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

    public void PublishDiagnostics(DafnyDocument document) {
      _languageServer.TextDocument.PublishDiagnostics(ToPublishDiagnostics(document));
    }

    public void HideDiagnostics(DafnyDocument document) {
      _languageServer.TextDocument.PublishDiagnostics(new PublishDiagnosticsParams {
        Uri = document.Uri,
        Version = document.Version,
        Diagnostics = new Container<Diagnostic>()
      });
    }

    private static PublishDiagnosticsParams ToPublishDiagnostics(DafnyDocument document) {
      return new() {
        Uri = document.Uri,
        Version = document.Version,
        Diagnostics = ToDiagnostics(document).ToArray(),
      };
    }

    private static IEnumerable<Diagnostic> ToDiagnostics(DafnyDocument document) {
      var reporter = (DiagnosticErrorReporter)document.Errors;
      return reporter.Diagnostics.Values.SelectMany(d => d);
      foreach (var entry in reporter.Diagnostics) {
        //if (document.Uri.Path == entry.Key) {
          return entry.Value;
        //}
      }

      return Enumerable.Empty<Diagnostic>();
    }

  }
}
