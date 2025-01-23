using System;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;
using XunitAssertMessages;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Util;

public class DiagnosticsReceiver : TestNotificationReceiver<PublishDiagnosticsParams> {


  static DiagnosticsReceiver() {
    StringifyUtil.AddGlobalOverride<DocumentUri>((par, writer) => {
      writer.Write(par.ToString());
    });
    StringifyUtil.AddGlobalOverride<Diagnostic>((par, writer) => {
      writer.Write(par.ToString());
    });
    StringifyUtil.AddGlobalOverride<PublishDiagnosticsParams>((par, writer) => {
      writer.Write($"{{ Uri: {par.Uri}, Diags: {par.Diagnostics.Stringify()} }}");
    });
  }

  public async Task<Diagnostic[]> AwaitNextWarningOrErrorDiagnosticsAsync(CancellationToken cancellationToken,
    TextDocumentItem textDocumentItem = null) {
    var result = await AwaitNextDiagnosticsAsync(cancellationToken, textDocumentItem);
    return result.Where(d => d.Severity <= DiagnosticSeverity.Warning).ToArray();
  }

  public Diagnostic[] GetLatestAndClearQueue(TextDocumentIdentifier document, DiagnosticSeverity minimumSeverity = DiagnosticSeverity.Warning) {
    var last = GetLatestAndClearQueue(d => d.Uri == document.Uri);
    return last?.Diagnostics.Where(d => d.Severity <= minimumSeverity).ToArray() ?? Array.Empty<Diagnostic>();
  }

  public async Task<Diagnostic[]> AwaitNextDiagnosticsAsync(CancellationToken cancellationToken,
    TextDocumentItem textDocumentItem = null) {
    var result = await AwaitNextNotificationAsync(cancellationToken);
    if (textDocumentItem != null) {
      // Before parsing finishes, the version can be null even for open files.
      var resultVersion = result.Version ?? textDocumentItem.Version;
      AssertM.Equal(textDocumentItem.Version, resultVersion,
        $"received incorrect version, diagnostics were: [{string.Join(", ", result.Diagnostics)}]");
      Assert.Equal(textDocumentItem.Uri, result.Uri);
    }
    return result.Diagnostics.ToArray();
  }

  public DiagnosticsReceiver(ILogger logger) : base(logger) {
  }
}
