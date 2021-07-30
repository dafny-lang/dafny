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
          TextDocument = documentUri.GetFileSystemPath()
        },
        CancellationToken
      );
    }

    [TestMethod]
    public async Task GetCounterExampleForFileWithBodylessMethodReturnsSingleCounterExampleForPostconditions() {
      var source = @"
method Abs(x: int) returns (y: int)
    ensures y > 0
{
}
".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual((2, 0), counterExamples[0].Position);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("y:int"));
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
      Assert.IsTrue(counterExamples[2].Variables.ContainsKey("x:int"));
      Assert.IsTrue(counterExamples[2].Variables.ContainsKey("y:int"));
      Assert.IsTrue(counterExamples[2].Variables.ContainsKey("z:int"));
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
    ensures y > 0
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
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("y:int"));
      Assert.AreEqual((7, 0), counterExamples[1].Position);
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("a:int"));
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("b:int"));
    }
    
    [TestMethod]
    public async Task GetCounterExampleForASelfReferringObject() {
      var source = @"
class Node {
    var next: Node?;
}

method IsSelfReferring(n:Node) returns (b:bool) {
    assert n.next != n;
}
".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("n:_module.Node?"));
    }
    
    [TestMethod]
    public async Task GetCounterExampleForAnObjectWithANonNullField() {
      var source = @"
class Node {
    var next: Node?;
}

method IsSelfRecursive(n:Node) returns (b:bool) {
    assert (n.next == n) || (n.next == null);
}
".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(2, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("n:_module.Node?"));
    }
    
    [TestMethod]
    public async Task GetCounterExampleForAnObjectWithANullField() {
      var source = @"
class Node {
    var next: Node?;
}

method IsSelfRecursive(n:Node) returns (b:bool) {
    assert n.next != null;
}
".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("n:_module.Node?"));
    }
    
    [TestMethod]
    public async Task GetCounterExampleWithTwoStatesAndPrimitiveField() {
      var source = @"
class BankAccountUnsafe {
    var balance: int;
    var b:bool;

    method withdraw(amount: int) 
        modifies this 
        requires amount >= 0
        requires balance >= 0 
        ensures balance >= 0
    {
      balance := balance - amount;   
    }
}
".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(2, counterExamples.Length);
      Assert.AreEqual(2, counterExamples[0].Variables.Count);
      Assert.AreEqual(2, counterExamples[1].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("amount:int"));
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("amount:int"));
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("this:_module.BankAccountUnsafe?"));
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("this:_module.BankAccountUnsafe?"));
    }
    
    [TestMethod]
    public async Task GetCounterExampleForACharacter() {
      var source = @"
method a(c:char) {
    assert c != '0';
}
".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("c:char"));
      Assert.IsTrue(counterExamples[0].Variables["c:char"] == "'0'");
    }
    
    [TestMethod]
    public async Task GetCounterExampleForADatatype() {
      var source = @"
datatype B = A(int)
method a(b:B) {
    assert b != A(5);
}
".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("b:_module.B"));
      // TODO: add more assertions here?
    }
    
    [TestMethod]
    public async Task GetCounterExampleForAnArray() {
      var source = @"
method a(arr:array<int>) requires arr.Length > 0 {
    assert arr[0] != 4;
}
".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("arr:_System.array?<int>"));
      // TODO: add more assertions here?
    }
    
    [TestMethod]
    public async Task GetCounterExampleForASequence() {
      var source = @"
method a(s:seq<int>) requires |s| > 0 {
    assert s[0] != 4;
}
".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("s:seq<int>"));
      // TODO: add more assertions here?
    }
    
    [TestMethod]
    public async Task GetCounterExampleForASequenceOfBitVectors() {
      var source = @"
method a(s:seq<bv5>) requires |s| > 0 {
    assert s[0] == (2 as bv5);
}
".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(2, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("s:seq<bv5>"));
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("@0:bv5"));
      // TODO: add more assertions here?
    }
  }
}
