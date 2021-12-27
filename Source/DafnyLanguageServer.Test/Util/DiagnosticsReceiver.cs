using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Util;

public class DiagnosticsReceiver : TestNotificationReceiver<PublishDiagnosticsParams> {

  public async Task<Diagnostic[]> AwaitNextDiagnosticsAsync(CancellationToken cancellationToken) {
    var result = await AwaitNextNotificationAsync(cancellationToken);
    return result.Diagnostics.ToArray();
  }
  public async Task<Diagnostic[]> AwaitVerificationDiagnosticsAsync(CancellationToken cancellationToken) {
    await AwaitNextNotificationAsync(cancellationToken);
    var result = await AwaitNextNotificationAsync(cancellationToken);
    return result.Diagnostics.ToArray();
  }

  // This change is to ensure that no diagnostics are remaining in the report queue.
  // var verificationDocumentItem = CreateTestDocument("class X {}", "verification.dfy");
  // await client.OpenDocumentAndWaitAsync(verificationDocumentItem, CancellationTokenWithHighTimeout);
  // var verificationReport = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationTokenWithHighTimeout);
  // Assert.AreEqual(verificationDocumentItem.Uri, verificationReport.Uri);
  public async Task<bool> AreMoreDiagnosticsComing(int timeout = 100) {
    var moreDiagnostics = AwaitNextNotificationAsync(CancellationToken.None);
    return await Task.WhenAny(moreDiagnostics, Task.Delay(timeout)) == moreDiagnostics;
  }
}