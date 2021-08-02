using System;
using Microsoft.Dafny.LanguageServer.Handlers.Custom;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using System.Linq;
using System.Text.RegularExpressions;
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
    public async Task FileWithBodyLessMethodReturnsSingleCounterExampleForPostconditions() {
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
      Assert.AreEqual((2, 6), counterExamples[0].Position);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("y:int"));
    }

    [TestMethod]
    public async Task FileWithMethodWithErrorsReturnsCounterExampleForPostconditionsAndEveryUpdateLine() {
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
      Assert.AreEqual((2, 6), counterExamples[0].Position);
      Assert.AreEqual((3, 18), counterExamples[1].Position);
      Assert.AreEqual((4, 14), counterExamples[2].Position);
      Assert.IsTrue(counterExamples[2].Variables.ContainsKey("x:int"));
      Assert.IsTrue(counterExamples[2].Variables.ContainsKey("y:int"));
      Assert.IsTrue(counterExamples[2].Variables.ContainsKey("z:int"));
    }

    [TestMethod]
    public async Task FileWithMethodWithoutErrorsReturnsEmptyCounterExampleList() {
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
      Assert.AreEqual((2, 6), counterExamples[0].Position);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("y:int"));
      Assert.AreEqual((7, 6), counterExamples[1].Position);
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("a:int"));
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("b:int"));
    }
    
    [TestMethod]
    public async Task SelfReferringObject() {
      var source = @"
      class Node {
          var next: Node?;
      }
      method IsSelfReferring(n:Node) {
          assert n.next != n;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("n:_module.Node?"));
      Assert.AreEqual("(next := n)", counterExamples[0].Variables["n:_module.Node?"]);
    }
    
    [TestMethod]
    public async Task RealFull() {
      var source = @"
      method a(r:real) {
          assert r != 1.0;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("r:real"));
      Assert.AreEqual("1.0", counterExamples[0].Variables["r:real"]);
    }
    
    [TestMethod]
    public async Task RealFraction() {
      var source = @"
      method a(r:real) {
          assert r != 0.4;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("r:real"));
      StringAssert.Matches(counterExamples[0].Variables["r:real"], new Regex("[0-9]+\\.[0-9]+/[0-9]+\\.[0-9]+"));
    }
    
    [TestMethod]
    public async Task RealFieldFull() {
      var source = @"
      class Value {
          var v:real;
      }
      method a(v:Value) {
          assert v.v != 0.0;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("v:_module.Value?"));
      Assert.AreEqual("(v := 0.0)", counterExamples[0].Variables["v:_module.Value?"]);
    }
    
    [TestMethod]
    public async Task RealFieldFraction() {
      var source = @"
      class Value {
          var v:real;
      }
      method a(v:Value) {
          assert v.v != 0.4;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("v:_module.Value?"));
      StringAssert.Matches(counterExamples[0].Variables["v:_module.Value?"], new Regex("\\(v := [0-9]+\\.[0-9]+/[0-9]+\\.[0-9]+\\)"));
    }
    
    [TestMethod]
    public async Task ObjectWithANonNullField() {
      var source = @"
      class Node {
          var next: Node?;
      }
      method IsSelfRecursive(n:Node) {
          assert (n.next == n) || (n.next == null);
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(2, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("n:_module.Node?"));
      StringAssert.Matches(counterExamples[0].Variables["n:_module.Node?"], new Regex("\\(next := @[0-9]+\\)"));
    }
    
    [TestMethod]
    public async Task ObjectWithANullField() {
      var source = @"
      class Node {
          var next: Node?;
      }
      method IsSelfRecursive(n:Node) {
          assert n.next != null;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("n:_module.Node?"));
      Assert.AreEqual("(next := null)", counterExamples[0].Variables["n:_module.Node?"]);
    }
    
    [TestMethod]
    public async Task PrimitiveField() {
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
      StringAssert.Matches(counterExamples[0].Variables["this:_module.BankAccountUnsafe?"], new Regex("\\(balance := [0-9]+\\)"));
      StringAssert.Matches(counterExamples[1].Variables["this:_module.BankAccountUnsafe?"], new Regex("\\(balance := \\-[0-9]+\\)"));
    }
    
    [TestMethod]
    public async Task Character() {
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
      Assert.AreEqual("'0'", counterExamples[0].Variables["c:char"]);
    }
    
    [TestMethod]
    public async Task UnknownCharacter() {
      var source = @"
      method a(c:char) {
          assert c == '0';
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("c:char"));
      StringAssert.Matches(counterExamples[0].Variables["c:char"], new Regex("('.'|\\?#[0-9]+)"));
      Assert.AreNotEqual(counterExamples[0].Variables["c:char"], "'0'");
    }
    
    [TestMethod]
    public async Task Datatype() {
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
      Assert.AreEqual("A([0] := 5)", counterExamples[0].Variables["b:_module.B"]);
    }
    
    [TestMethod]
    public async Task Array() {
      var source = @"
      method a(arr:array<int>) requires arr.Length == 2 {
          assert arr[0] != 4 || arr[1] != 5;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("arr:_System.array?<int>"));
      Assert.AreEqual("(Length := 2, [0] := 4, [1] := 5)", counterExamples[0].Variables["arr:_System.array?<int>"]);
    }
    
    [TestMethod]
    public async Task Sequence() {
      var source = @"
      method a(s:seq<int>) requires |s| == 1 {
          assert s[0] != 4;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("s:seq<int>"));
      Assert.AreEqual("(Length := 1, [0] := 4)", counterExamples[0].Variables["s:seq<int>"]);
    }
    
    [TestMethod]
    public async Task SequenceOfBitVectors() {
      var source = @"
      method a(s:seq<bv5>) requires |s| == 2 {
          assert s[1] != (2 as bv5);
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("s:seq<bv5>"));
      Assert.AreEqual("(Length := 2, [1] := 2bv5)", counterExamples[0].Variables["s:seq<bv5>"]);
    }
    
    [TestMethod]
    public async Task BitVector() {
      var source = @"
      method a(bv:bv7) {
          assert bv != (2 as bv7);
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("bv:bv7"));
      Assert.AreEqual("2bv7", counterExamples[0].Variables["bv:bv7"]);
    }
    
    [TestMethod]
    public async Task UnknownBitVector() {
      var source = @"
      method a(b:bv2) {
          assert b == (1 as bv2);
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("b:bv2"));
      StringAssert.Matches(counterExamples[0].Variables["b:bv2"], new Regex("[023]bv2"));
    }
    
    [TestMethod]
    public async Task BitWiseAnd() {
      var source = @"
      method m(a:bv1, b:bv1) {
          assert a & b != (1 as bv1);
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(2, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("a:bv1"));
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("b:bv1"));
      Assert.AreEqual("1bv1", counterExamples[0].Variables["a:bv1"]);
      Assert.AreEqual("1bv1", counterExamples[0].Variables["b:bv1"]);
    }
    
    [TestMethod]
    public async Task BitVectorField() {
      var source = @"
      class Value {
          var b:bv5;
      }
      method a(v:Value) {
          assert v.b != (2 as bv5);
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("v:_module.Value?"));
      Assert.AreEqual("(b := 2bv5)", counterExamples[0].Variables["v:_module.Value?"]);
    }
    
    [TestMethod]
    public async Task SetOfSeqOfSetOfArray() {
      var source = @"
      method a(s:set<seq<set<array<int>>>>) requires |s| <= 1{
          assert |s| == 0;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("s:set<seq<set<_System.array<int>>>>"));
      StringAssert.Matches(counterExamples[0].Variables["s:set<seq<set<_System.array<int>>>>"], new Regex("\\(@[0-9]+ := true\\)"));
    }
    
    [TestMethod]
    public async Task MultiDimensionalArray() {
      var source = @"
      method m(a:array3<int>) requires a.Length0 == 4 requires a.Length1 == 5 requires a.Length2 == 6 {
          assert a[2, 3, 1] != 7;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("a:_System.array3?<int>"));
      Assert.AreEqual("(Length0 := 4, Length1 := 5, Length2 := 6, [2,3,1] := 7)", counterExamples[0].Variables["a:_System.array3?<int>"]);
    }
    
    [TestMethod]
    public async Task Sets() {
      var source = @"
      method a(s1:set<char>, s2:set<char>) {
          var sUnion:set<char> := s1 + s2;
          var sInter:set<char> := s1 * s2;
          var sDiff:set<char> := s1 - s2;
          assert !('a' in sUnion) || ('a' in sInter) || !('b' in sInter) || !('a' in sDiff);
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(4, counterExamples.Length);
      Assert.AreEqual(5, counterExamples[2].Variables.Count);
      Assert.IsTrue(counterExamples[3].Variables.ContainsKey("s1:set<char>"));
      Assert.IsTrue(counterExamples[3].Variables.ContainsKey("s2:set<char>"));
      Assert.IsTrue(counterExamples[3].Variables.ContainsKey("sUnion:set<char>"));
      Assert.IsTrue(counterExamples[3].Variables.ContainsKey("sInter:set<char>"));
      Assert.IsTrue(counterExamples[3].Variables.ContainsKey("sDiff:set<char>"));
      var s1 = counterExamples[3].Variables["s1:set<char>"][1..^1].Split(", ");
      var s2 = counterExamples[3].Variables["s2:set<char>"][1..^1].Split(", ");
      var sUnion = counterExamples[3].Variables["sUnion:set<char>"][1..^1].Split(", ");
      var sInter = counterExamples[3].Variables["sInter:set<char>"][1..^1].Split(", ");
      var sDiff = counterExamples[3].Variables["sDiff:set<char>"][1..^1].Split(", ");
      Assert.IsTrue(s1.Contains("'a' := true"));
      Assert.IsTrue(s2.Contains("'a' := false"));
      Assert.IsTrue(sDiff.Contains("'a' := true"));
      Assert.IsTrue(sUnion.Contains("'a' := true"));
      Assert.IsTrue(sInter.Contains("'a' := false"));
      Assert.IsTrue(s1.Contains("'b' := true"));
      Assert.IsTrue(s2.Contains("'b' := true"));
      Assert.IsTrue(sDiff.Contains("'b' := false"));
      Assert.IsTrue(sUnion.Contains("'b' := true"));
      Assert.IsTrue(sInter.Contains("'b' := true"));
    }
    
    [TestMethod]
    public async Task StringBuilding() {
      var source = "" +
      "method a(s:string) {" + 
      "    assert s != \"abc\";"+
      "    }".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("s:seq<char>"));
      Assert.AreEqual("(Length := 3, [0] := 'a', [1] := 'b', [2] := 'c')", counterExamples[0].Variables["s:seq<char>"]);
    }
    
    [TestMethod]
    public async Task SequenceEdit() {
      var source = "" + 
      "method a(c:char, s1:string) requires s1 == \"abc\"{" +
      "    var s2:string := s1[1 := c];" +
      "    assert s2[0] != 'a' || s2[1] !='d' || s2[2] != 'c';}".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(2, counterExamples.Length);
      Assert.AreEqual(3, counterExamples[1].Variables.Count);
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("s1:seq<char>"));
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("s2:seq<char>"));
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("c:char"));
      Assert.AreEqual("(Length := 3, [0] := 'a', [1] := 'b', [2] := 'c')", counterExamples[1].Variables["s1:seq<char>"]);
      Assert.AreEqual("(Length := 3, [0] := 'a', [1] := 'd', [2] := 'c')", counterExamples[1].Variables["s2:seq<char>"]);
      Assert.AreEqual("'d'", counterExamples[1].Variables["c:char"]);
    }
    
    [TestMethod]
    public async Task SequenceConcat() {
      var source = @"
      method a(s1:string, s2:string) requires |s1| == 1 && |s2| == 1 {
          var sCat:string := s2 + s1;
          assert sCat[0] != 'a' || sCat[1] != 'b';
      }".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(2, counterExamples.Length);
      Assert.AreEqual(3, counterExamples[1].Variables.Count);
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("s1:seq<char>"));
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("s2:seq<char>"));
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("sCat:seq<char>"));
      Assert.AreEqual("(Length := 1, [0] := 'b')", counterExamples[1].Variables["s1:seq<char>"]);
      Assert.AreEqual("(Length := 1, [0] := 'a')", counterExamples[1].Variables["s2:seq<char>"]);
      Assert.AreEqual("(Length := 2, [0] := 'a', [1] := 'b')", counterExamples[1].Variables["sCat:seq<char>"]);
    }
    
    [TestMethod]
    public async Task SequenceGenerate() {
      var source = @"
      method a(multiplier:int) {
          var s:seq<int> := seq(3, i => i * multiplier);
          assert s[2] != 6;
      }".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(2, counterExamples.Length);
      Assert.AreEqual(4, counterExamples[1].Variables.Count);
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("multiplier:int"));
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("s:seq<int>"));
      StringAssert.Matches(counterExamples[1].Variables["s:seq<int>"], new Regex("\\(Length := 3, .*\\[2\\] := 6.*\\)"));
      Assert.AreEqual("3", counterExamples[1].Variables["multiplier:int"]);
    }

    [TestMethod]
    public async Task SequenceSub() {
      var source = @"
      method a(s:seq<char>) requires |s| == 5 {
          var sSub:seq<char> := s[2..4];
          assert sSub[0] != 'a' || sSub[1] != 'b';
      }".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(2, counterExamples.Length);
      Assert.AreEqual(2, counterExamples[1].Variables.Count);
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("sSub:seq<char>"));
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("s:seq<char>"));
      Assert.AreEqual("(Length := 2, [0] := 'a', [1] := 'b')", counterExamples[1].Variables["sSub:seq<char>"]);
      StringAssert.Matches(counterExamples[0].Variables["s:seq<char>"], new Regex("\\(Length := 5,.*\\[2\\] := 'a', \\[3\\] := 'b'.*"));
    }
    
    [TestMethod]
    public async Task SequenceDrop() {
      var source = @"
      method a(s:seq<char>) requires |s| == 5 {
          var sSub:seq<char> := s[2..];
          assert sSub[0] != 'a' || sSub[1] != 'b' || sSub[2] != 'c';
      }".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(2, counterExamples.Length);
      Assert.AreEqual(2, counterExamples[1].Variables.Count);
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("sSub:seq<char>"));
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("s:seq<char>"));
      Assert.AreEqual("(Length := 3, [0] := 'a', [1] := 'b', [2] := 'c')", counterExamples[1].Variables["sSub:seq<char>"]);
      StringAssert.Matches(counterExamples[0].Variables["s:seq<char>"], new Regex("\\(Length := 5,.*\\[2\\] := 'a', \\[3\\] := 'b', \\[4\\] := 'c'.*"));
    }
    
    [TestMethod]
    public async Task SequenceTake() {
      var source = @"
      method a(s:seq<char>) requires |s| == 5 {
          var sSub:seq<char> := s[..3];
          assert sSub[0] != 'a' || sSub[1] != 'b' || sSub[2] != 'c';
      }".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(2, counterExamples.Length);
      Assert.AreEqual(2, counterExamples[1].Variables.Count);
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("sSub:seq<char>"));
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("s:seq<char>"));
      Assert.AreEqual("(Length := 3, [0] := 'a', [1] := 'b', [2] := 'c')", counterExamples[1].Variables["sSub:seq<char>"]);
      StringAssert.Matches(counterExamples[0].Variables["s:seq<char>"], new Regex("\\(Length := 5,.*\\[0\\] := 'a', \\[1\\] := 'b', \\[2\\] := 'c'.*"));
    }
  }
}
