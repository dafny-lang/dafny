using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using JetBrains.Annotations;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Util;

public class DiagnosticsReceiver : TestNotificationReceiver<PublishDiagnosticsParams> {

  public async Task<Diagnostic[]> AwaitNextDiagnosticsAsync(CancellationToken cancellationToken,
    TextDocumentItem textDocumentItem = null) {
    var result = await AwaitNextNotificationAsync(cancellationToken);
    if (textDocumentItem != null) {
      Assert.AreEqual(textDocumentItem.Version, result.Version);
      Assert.AreEqual(textDocumentItem.Uri, result.Uri);
    }
    return result.Diagnostics.ToArray();
  }

  public async Task<Diagnostic[]> AwaitVerificationDiagnosticsAsync(CancellationToken cancellationToken) {
    var resolutionDiagnostics = await AwaitNextDiagnosticsAsync(cancellationToken);
    Assert.AreEqual(0, resolutionDiagnostics.Count(d => d.Source != MessageSource.Verifier.ToString()));
    return await AwaitNextDiagnosticsAsync(cancellationToken);
  }
}