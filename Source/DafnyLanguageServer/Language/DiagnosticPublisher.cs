using Microsoft.Dafny.LanguageServer.Util;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Server;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny.LanguageServer.Language {
  public class DiagnosticPublisher : IDiagnosticPublisher {
    private readonly ILanguageServerFacade _languageServer;

    public DiagnosticPublisher(ILanguageServerFacade languageServer) {
      _languageServer = languageServer;
    }

    public void PublishDiagnostics(DafnyDocument document) {
      if (document.LoadCanceled) {
        // We leave the responsibility to shift the error locations to the LSP clients.
        // Therefore, we do not republish the errors when the document (re-)load was canceled.
        return;
      }
      _languageServer.TextDocument.PublishDiagnostics(ToPublishDiagnostics(document));
    }

    public void HideDiagnostics(TextDocumentIdentifier documentId) {
      _languageServer.TextDocument.PublishDiagnostics(new PublishDiagnosticsParams {
        Uri = documentId.Uri,
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
      // Only report errors of the entry-document.
      if (document.Errors.Diagnostics.TryGetValue(document.GetFilePath(), out var diagnostics)) {
        return diagnostics;
      }
      return Enumerable.Empty<Diagnostic>();
    }
  }
}
