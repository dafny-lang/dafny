using System.Collections.Generic;
using System.IO;
using Microsoft.Dafny.LanguageServer.Handlers.Custom;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Workspace;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various {
  [TestClass]
  public class CounterExampleTest : ClientBasedLanguageServerTest {

    private Task<CounterExampleList> RequestCounterExamples(DocumentUri documentUri) {
      return client.SendRequest(
        new CounterExampleParams {
          TextDocument = documentUri.GetFileSystemPath()
        },
        CancellationToken
      );
    }

    [TestMethod]
    public async Task CounterexamplesStillWorksIfNothingHasBeenVerified() {
      await SetUp(options => options.Set(ServerCommand.Verification, VerifyOnMode.Never));
      var source = @"
      method Abs(x: int) returns (y: int)
        ensures y > 0
      {
      }
      ".TrimStart();
      await SetUp(o => o.Set(CommonOptionBag.RelaxDefiniteAssignment, true));
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual((2, 6), counterExamples[0].Position);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("y:int"));
    }

    [TestMethod]
    public async Task FileWithBodyLessMethodReturnsSingleCounterExampleForPostconditions() {
      var source = @"
      method Abs(x: int) returns (y: int)
        ensures y > 0
      {
      }
      ".TrimStart();
      await SetUp(o => o.Set(CommonOptionBag.RelaxDefiniteAssignment, true));
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
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
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
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
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
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

      await SetUp(o => o.Set(CommonOptionBag.RelaxDefiniteAssignment, true));

      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri))
        .OrderBy(counterExample => counterExample.Position)
        .ToArray();
      Assert.AreEqual(2, counterExamples.Length);
      Assert.AreEqual((2, 6), counterExamples[0].Position);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("y:int"));
      Assert.AreEqual((7, 6), counterExamples[1].Position);
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("a:int"));
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("b:int"));
    }

    [TestMethod]
    public async Task WholeNumberAsReal() {
      var source = @"
      method a(r:real) {
        assert r != 1.0;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("r:real"));
      Assert.AreEqual("1.0", counterExamples[0].Variables["r:real"]);
    }

    [TestMethod]
    public async Task FractionAsAReal() {
      var source = @"
      method a(r:real) {
        assert r != 0.4;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("r:real"));
      StringAssert.Matches(counterExamples[0].Variables["r:real"], new Regex("[0-9]+\\.[0-9]+/[0-9]+\\.[0-9]+"));
    }

    [TestMethod]
    public async Task WholeNumberFieldAsReal() {
      var source = @"
      class Value {
        var v:real;
      }
      method a(v:Value) {
        assert v.v != 0.0;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("v:_module.Value?"));
      Assert.AreEqual("(v := 0.0)", counterExamples[0].Variables["v:_module.Value?"]);
    }

    [TestMethod]
    public async Task FractionFieldAsReal() {
      var source = @"
      class Value {
        var v:real;
      }
      method a(v:Value) {
        assert v.v != 0.4;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("v:_module.Value?"));
      StringAssert.Matches(counterExamples[0].Variables["v:_module.Value?"], new Regex("\\(v := [0-9]+\\.[0-9]+/[0-9]+\\.[0-9]+\\)"));
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
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("n:_module.Node?"));
      Assert.AreEqual("(next := n)", counterExamples[0].Variables["n:_module.Node?"]);
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
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
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
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("n:_module.Node?"));
      Assert.AreEqual("(next := null)", counterExamples[0].Variables["n:_module.Node?"]);
    }

    [TestMethod]
    public async Task ObjectWithAFieldOfBasicType() {
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
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
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
    public async Task SpecificCharacter() {
      var source = @"
      method a(c:char) {
        assert c != '0';
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("c:char"));
      Assert.AreEqual("'0'", counterExamples[0].Variables["c:char"]);
    }

    [TestMethod]
    public async Task ArbitraryCharacter() {
      var source = @"
      method a(c:char) {
        assert c == '0';
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("c:char"));
      StringAssert.Matches(counterExamples[0].Variables["c:char"], new Regex("('.'|\\?#[0-9]+)"));
      Assert.AreNotEqual(counterExamples[0].Variables["c:char"], "'0'");
    }

    [TestMethod]
    public async Task DatatypeWithUnnamedDestructor() {
      var source = @"
      datatype B = A(int)
      method a(b:B) {
        assert b != A(5);
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("b:_module.B"));
      Assert.AreEqual("A(_h0 := 5)", counterExamples[0].Variables["b:_module.B"]);
    }

    [TestMethod]
    public async Task DatatypeWithDestructorThanIsADataValue() {
      var source = @"
      datatype A = B(x:real)
      method destructorNameTest(a:A) {
        assert a.x >= 0.0 || a.x < -0.5;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("a:_module.A"));
      StringAssert.Matches(counterExamples[0].Variables["a:_module.A"], new Regex("B\\(x := -[0-9]+\\.[0-9]+/[0-9]+\\.[0-9]+\\)"));
    }

    [TestMethod]
    public async Task DatatypeWithDifferentDestructorsForDifferentConstructors() {
      var source = @"
      datatype Hand = Left(x:int, y:int) | Right(a:int, b:int)
      method T_datatype0_1(h0:Hand, h1:Hand)
        requires h0.Right? && h1.Left? {
        assert h0 == h1;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(2, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("h0:_module.Hand"));
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("h1:_module.Hand"));
      StringAssert.Matches(counterExamples[0].Variables["h0:_module.Hand"], new Regex("Right\\([a|b] := -?[0-9]+, [b|a] := -?[0-9]+\\)"));
      StringAssert.Matches(counterExamples[0].Variables["h1:_module.Hand"], new Regex("Left\\([x|y] := -?[0-9]+, [x|y] := -?[0-9]+\\)"));
    }

    [TestMethod]
    public async Task DatatypeObjectWithTwoDestructorsWhoseValuesAreEqual() {
      var source = @"
      datatype Hand = Left(a:int, b:int)
      method T_datatype0_1(h:Hand)  {
        assert h.a != h.b || h.a != 3;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("h:_module.Hand"));
      StringAssert.Matches(counterExamples[0].Variables["h:_module.Hand"], new Regex("Left\\([a|b] := 3, [a|b] := 3\\)"));
    }

    [TestMethod]
    public async Task DatatypeWithDestructorsWhoseNamesShadowBuiltInDestructors() {
      var source = @"
      datatype A = B_(C_q:bool, B_q:bool, D_q:bool) | C(B_q:bool, C_q:bool, D_q:bool)
      method m (a:A) requires !a.B_?{
        assert a.C_q || a.B_q || a.D_q;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("a:_module.A"));
      StringAssert.Matches(counterExamples[0].Variables["a:_module.A"], new Regex("[B|C]\\((B__q|C__q|D__q) := false, (B__q|C__q|D__q) := false, (B__q|C__q|D__q) := false\\)"));
    }


    [TestMethod]
    public async Task DatatypeWithTypeParameters() {
      var source = @"
      datatype A<T> = One(b:T) | Two(i:int)
      method m(a:A<bool>) requires a == One(false) || a == One(true) {
        assert a.b;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("a:_module.A<bool>"));
      Assert.AreEqual("One(b := false)", counterExamples[0].Variables["a:_module.A<bool>"]);
    }

    [TestMethod]
    public async Task ArbitraryBool() {
      var source = @"
      datatype List<T> = Nil | Cons(head: T, tail: List<T>)
      method listHasSingleElement(list:List<bool>)
        requires list != Nil
      {
        assert list.tail != Nil;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(2, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("list:_module.List<bool>"));
      StringAssert.Matches(counterExamples[0].Variables["list:_module.List<bool>"], new Regex("Cons\\(head := (true|false), tail := @[0-9]+\\)"));
    }

    [TestMethod]
    public async Task ArbitraryInt() {
      var source = @"
      datatype List<T> = Nil | Cons(head: T, tail: List<T>)
      method listHasSingleElement(list:List<int>)
        requires list != Nil
      {
        assert list.tail != Nil;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(2, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("list:_module.List<int>"));
      StringAssert.Matches(counterExamples[0].Variables["list:_module.List<int>"], new Regex("Cons\\(head := -?[0-9]+, tail := @[0-9]+\\)"));
    }

    [TestMethod]
    public async Task ArbitraryReal() {
      var source = @"
      datatype List<T> = Nil | Cons(head: T, tail: List<T>)
      method listHasSingleElement(list:List<real>)
        requires list != Nil
      {
        assert list.tail != Nil;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(2, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("list:_module.List<real>"));
      StringAssert.Matches(counterExamples[0].Variables["list:_module.List<real>"], new Regex("Cons\\(head := -?[0-9]+\\.[0-9], tail := @[0-9]+\\)"));
    }

    [TestMethod]
    public async Task ArraySimpleTest() {
      var source = @"
      method a(arr:array<int>) requires arr.Length == 2 {
        assert arr[0] != 4 || arr[1] != 5;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("arr:_System.array?<int>"), string.Join(", ", counterExamples[0].Variables));
      Assert.AreEqual("(Length := 2, [0] := 4, [1] := 5)", counterExamples[0].Variables["arr:_System.array?<int>"]);
    }

    [TestMethod]
    public async Task SequenceSimpleTest() {
      var source = @"
      method a(s:seq<int>) requires |s| == 1 {
        assert s[0] != 4;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("s:seq<int>"));
      Assert.AreEqual("[4]", counterExamples[0].Variables["s:seq<int>"]);
    }

    [TestMethod]
    public async Task SequenceOfBitVectors() {
      var source = @"
      method a(s:seq<bv5>) requires |s| == 2 {
        assert s[1] != (2 as bv5);
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("s:seq<bv5>"));
      Assert.AreEqual("(Length := 2, [1] := 2)", counterExamples[0].Variables["s:seq<bv5>"]);
    }

    [TestMethod]
    public async Task SpecificBitVector() {
      var source = @"
      method a(bv:bv7) {
        assert bv != (2 as bv7);
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("bv:bv7"));
      Assert.AreEqual("2", counterExamples[0].Variables["bv:bv7"]);
    }

    [TestMethod]
    public async Task ArbitraryBitVector() {
      var source = @"
      method a(b:bv2) {
        assert b == (1 as bv2);
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("b:bv2"));
      StringAssert.Matches(counterExamples[0].Variables["b:bv2"], new Regex("[023]"));
    }

    [TestMethod]
    public async Task BitWiseAnd() {
      var source = @"
      method m(a:bv1, b:bv1) {
        assert a & b != (1 as bv1);
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(2, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("a:bv1"));
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("b:bv1"));
      StringAssert.Matches(counterExamples[0].Variables["a:bv1"], new Regex("(1|b)"));
      StringAssert.Matches(counterExamples[0].Variables["b:bv1"], new Regex("(1|a)"));
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
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("v:_module.Value?"));
      Assert.AreEqual("(b := 2)", counterExamples[0].Variables["v:_module.Value?"]);
    }

    [TestMethod]
    public async Task SeqSetAndArrayAsTypeParameters() {
      var source = @"
      method a(s:set<seq<set<array<int>>>>) requires |s| <= 1{
        assert |s| == 0;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("s:set<seq<set<_System.array<int>>>>"));
      StringAssert.Matches(counterExamples[0].Variables["s:set<seq<set<_System.array<int>>>>"], new Regex("\\{@[0-9]+ := true\\}"));
    }

    [TestMethod]
    public async Task MultiDimensionalArray() {
      var source = @"
      method m(a:array3<int>) requires a.Length0 == 4 requires a.Length1 == 5 requires a.Length2 == 6 {
        assert a[2, 3, 1] != 7;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("a:_System.array3?<int>"), string.Join(", ", counterExamples[0].Variables));
      Assert.AreEqual("(Length0 := 4, Length1 := 5, Length2 := 6, [2,3,1] := 7)", counterExamples[0].Variables["a:_System.array3?<int>"]);
    }

    [TestMethod]
    public async Task ArrayEqualityByReference() {
      var source = @"
      method test(x:array<int>, y:array<int>)   {
        assert x != y;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(2, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("x:_System.array?<int>"));
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("y:_System.array?<int>"));
      Assert.IsTrue(counterExamples[0].Variables["y:_System.array?<int>"] == "x" || counterExamples[0].Variables["x:_System.array?<int>"] == "y");
    }

    [TestMethod]
    public async Task SetBasicOperations() {
      var source = @"
      method a(s1:set<char>, s2:set<char>) {
        var sUnion:set<char> := s1 + s2;
        var sInter:set<char> := s1 * s2;
        var sDiff:set<char> := s1 - s2;
        assert !('a' in sUnion) || ('a' in sInter) || !('b' in sInter) || !('a' in sDiff);
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
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
    public async Task SetSingleElement() {
      var source = @"
      method test() {
        var s := {6};
        assert 6 !in s;
      }".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(2, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[1].Variables.Count);
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("s:set<int>"));
      StringAssert.Matches(counterExamples[1].Variables["s:set<int>"], new Regex("\\{.*6 := true.*\\}"));
    }

    [TestMethod]
    public async Task StringBuilding() {
      var source = "" +
      "method a(s:string) {" +
      "  assert s != \"abc\";" +
      "  }".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("s:seq<char>"));
      Assert.AreEqual("['a', 'b', 'c']", counterExamples[0].Variables["s:seq<char>"]);
    }

    [TestMethod]
    public async Task SequenceEdit() {
      var source = "" +
      "method a(c:char, s1:string) requires s1 == \"abc\"{" +
      "  var s2:string := s1[1 := c];" +
      "  assert s2[0] != 'a' || s2[1] !='d' || s2[2] != 'c';}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(2, counterExamples.Length);
      Assert.AreEqual(3, counterExamples[1].Variables.Count);
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("s1:seq<char>"));
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("s2:seq<char>"));
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("c:char"));
      Assert.AreEqual("['a', 'b', 'c']", counterExamples[1].Variables["s1:seq<char>"]);
      Assert.AreEqual("['a', 'd', 'c']", counterExamples[1].Variables["s2:seq<char>"]);
      Assert.AreEqual("'d'", counterExamples[1].Variables["c:char"]);
    }

    [TestMethod]
    public async Task SequenceSingleElement() {
      var source = @"
      method test() {
        var s := [6];
        assert 6 !in s;
      }".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(2, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[1].Variables.Count);
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("s:seq<int>"));
      StringAssert.Matches(counterExamples[1].Variables["s:seq<int>"], new Regex("\\[6\\]"));
    }

    [TestMethod]
    public async Task SequenceConcat() {
      var source = @"
      method a(s1:string, s2:string) requires |s1| == 1 && |s2| == 1 {
        var sCat:string := s2 + s1;
        assert sCat[0] != 'a' || sCat[1] != 'b';
      }".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(2, counterExamples.Length);
      Assert.AreEqual(3, counterExamples[1].Variables.Count);
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("s1:seq<char>"));
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("s2:seq<char>"));
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("sCat:seq<char>"));
      Assert.AreEqual("['b']", counterExamples[1].Variables["s1:seq<char>"]);
      Assert.AreEqual("['a']", counterExamples[1].Variables["s2:seq<char>"]);
      Assert.AreEqual("['a', 'b']", counterExamples[1].Variables["sCat:seq<char>"]);
    }

    [TestMethod]
    public async Task SequenceGenerate() {
      var source = @"
      method a(multiplier:int) {
        var s:seq<int> := seq(3, i => i * multiplier);
        assert s[2] != 6;
      }".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(2, counterExamples.Length);
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
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(2, counterExamples.Length);
      Assert.AreEqual(2, counterExamples[1].Variables.Count);
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("sSub:seq<char>"));
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("s:seq<char>"));
      Assert.AreEqual("['a', 'b']", counterExamples[1].Variables["sSub:seq<char>"]);
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
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(2, counterExamples.Length);
      Assert.AreEqual(2, counterExamples[1].Variables.Count);
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("sSub:seq<char>"));
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("s:seq<char>"));
      Assert.AreEqual("['a', 'b', 'c']", counterExamples[1].Variables["sSub:seq<char>"]);
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
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(2, counterExamples.Length);
      Assert.AreEqual(2, counterExamples[1].Variables.Count);
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("sSub:seq<char>"));
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("s:seq<char>"));
      Assert.AreEqual("['a', 'b', 'c']", counterExamples[1].Variables["sSub:seq<char>"]);
      StringAssert.Matches(counterExamples[0].Variables["s:seq<char>"], new Regex("\\(Length := 5,.*\\[0\\] := 'a', \\[1\\] := 'b', \\[2\\] := 'c'.*"));
    }

    [TestMethod]
    public async Task VariableNameShadowing() {
      var source = @"
      method test(m:set<int>) {
        var m := {6};
        assert 6 !in m;
      }".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(2, counterExamples.Length);
    }

    [TestMethod]
    public async Task MapsCreation() {
      var source = @"
      method test() {
        var m := map[3 := false];
        assert m[3];
      }".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(2, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[1].Variables.Count);
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("m:map<int, bool>"));
      StringAssert.Matches(counterExamples[1].Variables["m:map<int, bool>"], new Regex("\\(.*3 := false.*"));
    }

    [TestMethod]
    public async Task MapsUpdate() {
      var source = @"
      method test(value:int) {
        var m := map[3 := -1];
        var b := m[3] == -1;
        m := m[3 := value];
        assert b && m[3] <= 0;
      }".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(4, counterExamples.Length);
      Assert.AreEqual(2, counterExamples[1].Variables.Count);
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("m:map<int, int>"));
      StringAssert.Matches(counterExamples[1].Variables["m:map<int, int>"], new Regex("\\(.*3 := -1.*"));
      Assert.AreEqual(3, counterExamples[3].Variables.Count);
      Assert.IsTrue(counterExamples[3].Variables.ContainsKey("m:map<int, int>"));
      Assert.IsTrue(counterExamples[3].Variables.ContainsKey("value:int"));
      Assert.IsTrue(counterExamples[3].Variables.ContainsKey("b:bool"));
      Assert.AreEqual("true", counterExamples[3].Variables["b:bool"]);
      StringAssert.Matches(counterExamples[3].Variables["value:int"], new Regex("[1-9][0-9]*"));
      StringAssert.Matches(counterExamples[3].Variables["m:map<int, int>"], new Regex("\\(.*3 := [1-9].*"));
    }

    [TestMethod]
    public async Task MapsUpdateStoredInANewVariable() {
      var source = @"
      method T_map1(m:map<int,int>, key:int, val:int)
        requires key in m.Keys
      {
        var m' := m[key := val - 1];
        m' := m'[key := val];
        assert m'.Values == m.Values - {m[key]} + {val};
      }".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(3, counterExamples.Length);
      Assert.AreEqual(4, counterExamples[2].Variables.Count);
      Assert.IsTrue(counterExamples[2].Variables.ContainsKey("m:map<int, int>"));
      Assert.IsTrue(counterExamples[2].Variables.ContainsKey("m':map<int, int>"));
      Assert.IsTrue(counterExamples[2].Variables.ContainsKey("val:int"));
      Assert.IsTrue(counterExamples[2].Variables.ContainsKey("key:int"));
      var key = counterExamples[2].Variables["key:int"];
      var val = counterExamples[2].Variables["val:int"];
      StringAssert.Matches(counterExamples[2].Variables["m':map<int, int>"], new Regex("\\(.*" + key + " := " + val + ".*"));
    }

    [TestMethod]
    public async Task MapsValuesUpdate() {
      // This corner case previously triggered infinite loops
      var source = @"
      method T_map0(m:map<int,int>, key:int, val:int)
      {
        var m' := m[key := val];
        assert m.Values + {val} == m'.Values;
      }".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(2, counterExamples.Length);
      Assert.AreEqual(4, counterExamples[1].Variables.Count);
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("m:map<int, int>"));
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("m':map<int, int>"));
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("val:int"));
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("key:int"));
      var key = counterExamples[1].Variables["key:int"];
      var val = counterExamples[1].Variables["val:int"];
      var mapRegex = new Regex("\\(.*" + key + " := " + val + ".*");
      Assert.IsTrue(mapRegex.IsMatch(counterExamples[1].Variables["m':map<int, int>"]) ||
                    mapRegex.IsMatch(counterExamples[1].Variables["m:map<int, int>"]));

    }

    [TestMethod]
    public async Task MapsKeys() {
      var source = @"
      method test(m:map<int,char>) {
        var keys := m.Keys;
        assert (25 !in keys);
      }".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(2, counterExamples.Length);
      Assert.AreEqual(2, counterExamples[1].Variables.Count);
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("m:map<int, char>"));
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("keys:set<int>"));
      StringAssert.Matches(counterExamples[1].Variables["m:map<int, char>"], new Regex("\\(.*25 := .*"));
      StringAssert.Matches(counterExamples[1].Variables["keys:set<int>"], new Regex("\\{.*25 := true.*"));
    }

    [TestMethod]
    public async Task MapsValues() {
      var source = @"
      method test(m:map<int,char>) {
        var values := m.Values;
        assert ('c' !in values);
      }".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(2, counterExamples.Length);
      Assert.AreEqual(2, counterExamples[1].Variables.Count);
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("m:map<int, char>"));
      Assert.IsTrue(counterExamples[1].Variables.ContainsKey("values:set<char>"));
      StringAssert.Matches(counterExamples[1].Variables["m:map<int, char>"], new Regex("\\(.* := 'c'.*"));
      StringAssert.Matches(counterExamples[1].Variables["values:set<char>"], new Regex("\\{.*'c' := true.*"));
    }

    [TestMethod]
    public async Task MapsOfBitVectors() {
      // This test case triggers a situation in which the model does not
      // specify concrete values for bit vectors and the counterexample extraction
      // tool has to come up with such a value
      var source = @"
      method test(m:map<bv2,bv3>) {
        assert |m| == 0;
      }".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("m:map<bv2, bv3>"));
      StringAssert.Matches(counterExamples[0].Variables["m:map<bv2, bv3>"], new Regex("\\(.*[0-9]+ := [0-9]+.*"));
    }

    [TestMethod]
    public async Task ModuleRenaming() {
      var source = @"
      module Mo_dule_ {
         module Module2_ {
            class Cla__ss {
               var i:int;
               method test() {
                  assert this.i != 5;
               }
            }
         }
      }".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.AreEqual(1, counterExamples[0].Variables.Count);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("this:Mo_dule_.Module2_.Cla__ss?"));
      Assert.AreEqual("(i := 5)", counterExamples[0].Variables["this:Mo_dule_.Module2_.Cla__ss?"]);
    }

    [TestMethod]
    public async Task UnboundedIntegers() {
      var source = @"
      ghost const NAT64_MAX := 0x7fff_ffff_ffff_ffff

      newtype nat64 = x | 0 <= x <= NAT64_MAX

      function method plus(a: nat64, b: nat64): nat64 {
        a + b
      }".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("a:int"));
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("b:int"));
      var a = long.Parse(counterExamples[0].Variables["a:int"]);
      var b = long.Parse(counterExamples[0].Variables["b:int"]);
      Assert.IsTrue(a + b < a || a + b < b);
    }

    [TestMethod]
    public async Task DatatypeWithPredicate() {
      var source = @"
      module M {
        datatype D = C(i:int) {
          predicate p() {true}
        }

        method test(d: D) {
          if (d.p()) {
            assert d.i != 123;
          }
        }
      }".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("d:M.D"));
      Assert.AreEqual("C(i := 123)", counterExamples[0].Variables["d:M.D"]);
    }

    /// <summary>
    /// Test a situation in which two fields of an object are equal
    /// (the value is represented by one Element in the Model)
    /// </summary>
    [TestMethod]
    public async Task EqualFields() {
      var source = @"
      module M {
        class C { 
          var c1:char;
          var c2:char;
        }

        method test(c: C?) {
          assert c == null || c.c1 != c.c2 || c.c1 != '\u1023';
        }
      }".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).ToArray();
      Assert.AreEqual(1, counterExamples.Length);
      Assert.IsTrue(counterExamples[0].Variables.ContainsKey("c:M.C?"));
      Assert.IsTrue(counterExamples[0].Variables["c:M.C?"] is
        "(c1 := '\\u1023', c2 := '\\u1023')" or
        "(c2 := '\\u1023', c1 := '\\u1023')");
    }

    /// <summary>
    /// Tests that a Dafny program where a sequence with non-integral indices is generated as part of
    /// a counterexample.  This would previously crash the LSP before #3093.
    /// For more details, see https://github.com/dafny-lang/dafny/issues/3048 .
    /// </summary>
    [TestMethod]
    public async Task NonIntegerSeqIndices() {
      string fp = Path.Combine(Directory.GetCurrentDirectory(), "Various", "TestFiles", "3048.dfy");
      var source = await File.ReadAllTextAsync(fp, CancellationToken);
      var documentItem = CreateTestDocument(source);

      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

      /* First, ensure we can correctly extract counterexamples without crashing... */
      var nonIntegralIndexedSeqs = (await RequestCounterExamples(documentItem.Uri))
        .SelectMany(cet => cet.Variables.ToList())
        /* Then, extract the number of non-integral indexed sequences from the repro case... */
        .Count(IsNegativeIndexedSeq);

      // With more recent Z3 versions (at least 4.11+, but maybe going back farther), this situation doesn't seem
      // to arise anymore. So this test now just confirms that the test file it loads can be verified without
      // crashing.
      /*
      Assert.IsTrue(nonIntegralIndexedSeqs > 0, "If we do not see at least one non-integral index in " +
                                                "this test case, then the backend changed " +
                                                "The indices being returned to the Language Server.");
                                                */
    }

    /* Helper for the NonIntegerSeqIndices test. */
    private static bool IsNegativeIndexedSeq(KeyValuePair<string, string> kvp) {
      var r = new Regex(@"\[\(- \d+\)\]");
      return kvp.Key.Contains("seq<_module.uint8>") && r.IsMatch(kvp.Value);
    }

    [TestMethod]
    public void TestIsNegativeIndexedSeq() {
      Assert.IsFalse(
        IsNegativeIndexedSeq(new KeyValuePair<string, string>("uint8", "42")));
      Assert.IsFalse(
        IsNegativeIndexedSeq(new KeyValuePair<string, string>("seq<_module.uint8>", "(Length := 42, [0] := 42)")));
      Assert.IsTrue(
        IsNegativeIndexedSeq(new KeyValuePair<string, string>("seq<_module.uint8>", "(Length := 9899, [(- 1)] := 42)")));
      Assert.IsTrue(
        IsNegativeIndexedSeq(new KeyValuePair<string, string>("seq<seq<_module.uint8>>", "(Length := 1123, [(- 12345)] := @12)")));
    }
  }
}
