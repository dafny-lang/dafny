using System;
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
      Assert.AreEqual(textDocumentItem.Version, result.Version,
        $"result diagnostics were: [{string.Join(", ", result.Diagnostics)}]");
      Assert.AreEqual(textDocumentItem.Uri, result.Uri);
    }
    return result.Diagnostics.ToArray();
  }
}