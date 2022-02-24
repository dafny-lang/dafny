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
  public class CancelVerificationTest : DafnyLanguageServerTestBase {
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
      client.OpenDocument(documentItem);
      await Task.Delay(5_000);
      // This cancels the previous request.
      client.DidChangeTextDocument(new DidChangeTextDocumentParams {
        TextDocument = new OptionalVersionedTextDocumentIdentifier {
          Uri = documentItem.Uri,
          Version = documentItem.Version + 1
        },
        ContentChanges = new[] {new TextDocumentContentChangeEvent {
          Range = new Range((12, 9), (12, 23)),
          Text = "true"
        }}
      });
      await client.WaitForNotificationCompletionAsync(documentItem.Uri, CancellationToken);
      var document = await Documents.GetDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      Assert.IsTrue(!document.Errors.HasErrors);
      client.DidChangeTextDocument(new DidChangeTextDocumentParams {
        TextDocument = new OptionalVersionedTextDocumentIdentifier {
          Uri = documentItem.Uri,
          Version = documentItem.Version + 2
        },
        ContentChanges = new[] {new TextDocumentContentChangeEvent {
          Range = new Range((12, 9), (12, 13)),
          Text = "/" // A parse error
        }}
      });
      await client.WaitForNotificationCompletionAsync(documentItem.Uri, CancellationToken);
      document = await Documents.GetDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      Assert.IsTrue(document.Errors.HasErrors);
    }
  }
}
