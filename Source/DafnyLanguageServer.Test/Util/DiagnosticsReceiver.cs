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
}