using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading.Tasks;

namespace DafnyLS.IntegrationTest {
  [TestClass]
  public class UnitTest1 : IntegrationTestBase {
    [TestMethod]
    public async Task TestMethod1() {
      var client = await InitializeClient();
      Assert.IsNotNull(client.ClientSettings);
      var completion = await client.RequestCompletion(new CompletionParams {
        TextDocument = DocumentUri.FromFileSystemPath("test.dfy")
      }, CancellationToken);
    }
  }
}
