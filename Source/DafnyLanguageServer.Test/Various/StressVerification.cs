using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using System.IO;
using System.Threading;
using System.Threading.Tasks;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various {
  [TestClass]
  public class StressVerificationTest : DafnyLanguageServerTestBase {
    private ILanguageClient client;

    [TestInitialize]
    public async Task SetUp() {
      client = await InitializeClient();
    }

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

method test() {
  assert Ack(5, 5) == 0;
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      var version = documentItem.Version;
      DidChangeTextDocumentParams ChangeRequest(int line, int character, int deleted, string added) {
        version += 1;
        return new DidChangeTextDocumentParams {
          TextDocument = new OptionalVersionedTextDocumentIdentifier {
            Uri = documentItem.Uri,
            Version = version
          },
          ContentChanges = new[] {new TextDocumentContentChangeEvent {
            Range = new Range((line - 1, character - 1), (line - 1, character - 1 + deleted)),
            Text = added
          }}
        };
      }

      client.OpenDocument(documentItem);
      await Task.Delay(1_000);
      var numberOfSpacesToAdd = 60;

      // Just add hundred spaces in 5 seconds
      for (var i = 1; i <= numberOfSpacesToAdd; i++) {
        client.DidChangeTextDocument(ChangeRequest(13, 10, 0, " "));
        await Task.Delay(i);
      }
      // This cancels the previous request.
      client.DidChangeTextDocument(ChangeRequest(13, 10, numberOfSpacesToAdd + 14, "true"));
      await client.WaitForNotificationCompletionAsync(documentItem.Uri, CancellationToken);
      var document = await Documents.GetDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      Assert.IsTrue(!document.Errors.HasErrors);
    }
  }
}
