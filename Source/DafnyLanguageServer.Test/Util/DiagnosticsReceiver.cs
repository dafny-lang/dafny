using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;
using Assert = XunitAssertMessages.AssertM;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Util;

public class DiagnosticsReceiver : TestNotificationReceiver<PublishDiagnosticsParams> {

  public async Task<Diagnostic[]> AwaitNextDiagnosticsAsync(CancellationToken cancellationToken,
    TextDocumentItem textDocumentItem = null) {
    var result = await AwaitNextNotificationAsync(cancellationToken);
    if (textDocumentItem != null) {
      Assert.Equal(textDocumentItem.Version, result.Version,
        $"result diagnostics were: [{string.Join(", ", result.Diagnostics)}]");
      Assert.Equal(textDocumentItem.Uri, result.Uri);
    }
    return result.Diagnostics.ToArray();
  }
}
