using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using JetBrains.Annotations;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Util;

public class DiagnosticsReceiver : TestNotificationReceiver<PublishDiagnosticsParams> {

  public async Task<Diagnostic[]> AwaitNextDiagnosticsAsync(CancellationToken cancellationToken, DocumentUri uri = null) {
    var result = await AwaitNextNotificationAsync(cancellationToken);
    if (uri != null) {
      Assert.AreEqual(uri, result.Uri, result.Uri + ", diagnostics: " + DafnyLanguageServerTestBase.PrintDiagnostics(result.Diagnostics));
    }
    return result.Diagnostics.ToArray();
  }
  public async Task<Diagnostic[]> AwaitVerificationDiagnosticsAsync(CancellationToken cancellationToken, [CanBeNull] DocumentUri uri = null) {
    var resolutionDiagnostics = await AwaitNextDiagnosticsAsync(cancellationToken);
    Assert.AreEqual(0, resolutionDiagnostics.Count(d => d.Code != "Verification"), DafnyLanguageServerTestBase.PrintDiagnostics(resolutionDiagnostics));
    return await AwaitNextDiagnosticsAsync(cancellationToken, uri);
  }
}