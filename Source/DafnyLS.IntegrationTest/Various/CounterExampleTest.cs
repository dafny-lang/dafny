using Microsoft.Dafny.LanguageServer.Handlers.Custom;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using System.Linq;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various {
  [TestClass]
  public class CounterExampleTest : DafnyLanguageServerTestBase {
    private ILanguageClient _client;

    [TestInitialize]
    public async Task SetUp() {
      _client = await InitializeClient();
    }

    private Task<CounterExampleList> RequestCounterExamples(DocumentUri documentUri) {
      return _client.SendRequest(
        new CounterExampleParams {
          DafnyFile = documentUri.GetFileSystemPath()
        },
        CancellationToken
      );
    }

    [TestMethod]
    public async Task GetCounterExampleForFileWithBodylessMethodReturnsSingleCounterExampleForPostconditions() {
      var source = @"
method Abs(x: int) returns (y: int)
    ensures y >= 0
{
}
".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual((2, 0), counterExamples[0].Position);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("x"));
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("y"));
    }

    [TestMethod]
    public async Task GetCounterExampleForFileWithMethodWithErrorsReturnsCounterExampleForPostconditionsAndEveryUpdateLine() {
      var source = @"
method Abs(x: int) returns (y: int)
    ensures y >= 0
{
  var z := x;
  y := z;
}
".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(3, counterExamples.Length);
      Assert.AreEqual((2, 0), counterExamples[0].Position);
      Assert.AreEqual((3, 12), counterExamples[1].Position);
      Assert.AreEqual((4, 8), counterExamples[2].Position);
      Assert.IsTrue(counterExamples[2].Variables.ContainsKey("x"));
      Assert.IsTrue(counterExamples[2].Variables.ContainsKey("y"));
      Assert.IsTrue(counterExamples[2].Variables.ContainsKey("z"));
    }

    [TestMethod]
    public async Task GetCounterExampleForFileWithMethodWithoutErrorsReturnsEmptyCounterExampleList() {
      var source = @"
method Abs(x: int) returns (y: int)
    ensures y >= 0
{
  if x >= 0 {
    return x;
  }
  return -x;
}
".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(0, counterExamples.Length);
    }

    [TestMethod]
    public async Task GetCounterExampleWithMultipleMethodsWithErrorsReturnsCounterExamplesForEveryMethod() {
      var source = @"
method Abs(x: int) returns (y: int)
    ensures y >= 0
{
}

method Negate(a: int) returns (b: int)
    ensures b == -a
{
}
".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(2, counterExamples.Length);
      Assert.AreEqual((2, 0), counterExamples[0].Position);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("x"));
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("y"));
      Assert.AreEqual((7, 0), counterExamples[1].Position);
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("a"));
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("b"));
    }
  }
}
