using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using System.IO;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various {
  [TestClass]
  public class CancelVerificationTest : ClientBasedLanguageServerTest {

    // https://github.com/dafny-lang/language-server-csharp/issues/40
    [TestMethod]
    public async Task CancelingVerificationStopsTheProver() {
      var source = @"
function method {:unroll 100} Ack(m: nat, n: nat): nat
  decreases m, n
{
  if m == 0 then
    n + 1
  else if n == 0 then
    Ack(m - 1, 1)
  else
    Ack(m - 1, Ack(m, n - 1))
}

method {:timeLimit 10} test() {
  assert Ack(5, 5) == 0;
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      client.OpenDocument(documentItem);
      await Task.Delay(5_000);

      // Cancels the previous request.
      ApplyChange(ref documentItem, new Range((12, 9), (12, 23)), "true");

      await client.WaitForNotificationCompletionAsync(documentItem.Uri, CancellationToken);
      var document = await Documents.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      Assert.IsTrue(!document.Diagnostics.Any());
      ApplyChange(ref documentItem, new Range((12, 9), (12, 13)), "/");
      await client.WaitForNotificationCompletionAsync(documentItem.Uri, CancellationToken);
      document = await Documents.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      Assert.IsTrue(document.Diagnostics.Any());
    }
  }
}
