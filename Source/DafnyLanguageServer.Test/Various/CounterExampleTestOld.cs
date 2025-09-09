using System;
using System.Collections.Generic;
using System.IO;
using Microsoft.Dafny.LanguageServer.Handlers.Custom;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using OmniSharp.Extensions.LanguageServer.Protocol;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various {
  static class StringAssert {
    public static void Matches(string value, Regex regex) {
      Assert.True(regex.Matches(value).Any());
    }
  }

  public class CounterExampleTest : ClientBasedLanguageServerTest {

    private Task<CounterExampleList> RequestCounterExamples(DocumentUri documentUri) {
      return client.SendRequest(
        new CounterExampleParams {
          TextDocument = documentUri.GetFileSystemPath()
        },
        CancellationToken
      );
    }

    public static TheoryData<Action<DafnyOptions>> OptionSettings() {
      var optionSettings = new TheoryData<Action<DafnyOptions>>();
      optionSettings.Add(options => options.TypeEncodingMethod = CoreOptions.TypeEncoding.Predicates);
      optionSettings.Add(options => options.TypeEncodingMethod = CoreOptions.TypeEncoding.Arguments);
      return optionSettings;
    }

    private async Task SetUpOptions(Action<DafnyOptions> optionSettings) {
      await SetUp(optionSettings);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task CounterexamplesStillWorksIfNothingHasBeenVerified(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      await SetUp(options => options.Set(ProjectManager.Verification, VerifyOnMode.Never));
      var source = @"
      method Abs(x: int) returns (y: int)
        ensures y > 0
      {
      }
      ".TrimStart();
      await SetUp(o => o.Set(CommonOptionBag.RelaxDefiniteAssignment, true));
      var documentItem = CreateTestDocument(source, "CounterexamplesStillWorksIfNothingHasBeenVerified.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.Equal((2, 6), counterExamples[0].Position);
      Assert.True(counterExamples[0].Variables.ContainsKey("y:int"));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task FileWithBodyLessMethodReturnsSingleCounterExampleForPostconditions(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      method Abs(x: int) returns (y: int)
        ensures y > 0
      {
      }
      ".TrimStart();
      await SetUp(o => o.Set(CommonOptionBag.RelaxDefiniteAssignment, true));
      var documentItem = CreateTestDocument(source, "FileWithBodyLessMethodReturnsSingleCounterExampleForPostconditions.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.Equal((2, 6), counterExamples[0].Position);
      Assert.True(counterExamples[0].Variables.ContainsKey("y:int"));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task FileWithMethodWithErrorsReturnsCounterExampleForPostconditionsAndEveryUpdateLine(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      method Abs(x: int) returns (y: int)
        ensures y >= 0
      {
        var z := x;
        y := z;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source, "FileWithMethodWithErrorsReturnsCounterExampleForPostconditionsAndEveryUpdateLine.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Equal(3, counterExamples.Length);
      Assert.Equal((2, 6), counterExamples[0].Position);
      Assert.Equal((3, 18), counterExamples[1].Position);
      Assert.Equal((4, 14), counterExamples[2].Position);
      Assert.True(counterExamples[2].Variables.ContainsKey("x:int"));
      Assert.True(counterExamples[2].Variables.ContainsKey("y:int"));
      Assert.True(counterExamples[2].Variables.ContainsKey("z:int"));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task FileWithMethodWithoutErrorsReturnsEmptyCounterExampleList(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
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
      var documentItem = CreateTestDocument(source, "FileWithMethodWithoutErrorsReturnsEmptyCounterExampleList.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Empty(counterExamples);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task GetCounterExampleWithMultipleMethodsWithErrorsReturnsCounterExamplesForEveryMethod(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
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

      var documentItem = CreateTestDocument(source, "GetCounterExampleWithMultipleMethodsWithErrorsReturnsCounterExamplesForEveryMethod.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri))
        .OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Equal(2, counterExamples.Length);
      Assert.Equal((2, 6), counterExamples[0].Position);
      Assert.True(counterExamples[0].Variables.ContainsKey("y:int"));
      Assert.Equal((7, 6), counterExamples[1].Position);
      Assert.True(counterExamples[1].Variables.ContainsKey("a:int"));
      Assert.True(counterExamples[1].Variables.ContainsKey("b:int"));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task WholeNumberAsReal(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      method a(r:real) {
        assert r != 1.0;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source, "WholeNumberAsReal.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.Equal(1, counterExamples[0].Variables.Count);
      Assert.True(counterExamples[0].Variables.ContainsKey("r:real"));
      Assert.Equal("1.0", counterExamples[0].Variables["r:real"]);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task FractionAsAReal(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      method a(r:real) {
        assert r != 0.4;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source, "FractionAsAReal.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.Equal(1, counterExamples[0].Variables.Count);
      Assert.True(counterExamples[0].Variables.ContainsKey("r:real"));
      StringAssert.Matches(counterExamples[0].Variables["r:real"], new Regex("[0-9]+\\.[0-9]+/[0-9]+\\.[0-9]+"));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task WholeNumberFieldAsReal(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      class Value {
        var v:real;
      }
      method a(v:Value) {
        assert v.v != 0.0;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source, "WholeNumberFieldAsReal.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.Equal(1, counterExamples[0].Variables.Count);
      Assert.True(counterExamples[0].Variables.ContainsKey("v:_module.Value"));
      Assert.Equal("(v := 0.0)", counterExamples[0].Variables["v:_module.Value"]);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task ConstantFields(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      class Value {
        const with_underscore_:int;
      }
      method a(v:Value) {
        assert v.with_underscore_ != 42;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source, "ConstantFields.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.Equal(1, counterExamples[0].Variables.Count);
      Assert.True(counterExamples[0].Variables.ContainsKey("v:_module.Value"));
      Assert.Equal("(with_underscore_ := 42)", counterExamples[0].Variables["v:_module.Value"]);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task FractionFieldAsReal(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      class Value {
        var v:real;
      }
      method a(v:Value) {
        assert v.v != 0.4;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source, "FractionFieldAsReal.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.Equal(1, counterExamples[0].Variables.Count);
      Assert.True(counterExamples[0].Variables.ContainsKey("v:_module.Value"));
      StringAssert.Matches(counterExamples[0].Variables["v:_module.Value"], new Regex("\\(v := [0-9]+\\.[0-9]+/[0-9]+\\.[0-9]+\\)"));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task SelfReferringObject(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      class Node {
        var next: Node?;
      }
      method IsSelfReferring(n:Node) {
        assert n.next != n;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source, "SelfReferringObject.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.Equal(1, counterExamples[0].Variables.Count);
      Assert.True(counterExamples[0].Variables.ContainsKey("n:_module.Node"));
      Assert.Equal("(next := n)", counterExamples[0].Variables["n:_module.Node"]);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task ObjectWithANonNullField(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      class Node {
        var next: Node?;
      }
      method IsSelfRecursive(n:Node) {
        assert (n.next == n) || (n.next == null);
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source, "ObjectWithANonNullField.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.Equal(2, counterExamples[0].Variables.Count);
      Assert.True(counterExamples[0].Variables.ContainsKey("n:_module.Node"));
      StringAssert.Matches(counterExamples[0].Variables["n:_module.Node"], new Regex("\\(next := @[0-9]+\\)"));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task ObjectWithANullField(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      class Node {
        var next: Node?;
      }
      method IsSelfRecursive(n:Node) {
        assert n.next != null;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source, "ObjectWithANullField.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.Equal(1, counterExamples[0].Variables.Count);
      Assert.True(counterExamples[0].Variables.ContainsKey("n:_module.Node"));
      Assert.Equal("(next := null)", counterExamples[0].Variables["n:_module.Node"]);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task ObjectWithAFieldOfBasicType(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
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
      var documentItem = CreateTestDocument(source, "ObjectWithAFieldOfBasicType.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Equal(2, counterExamples.Length);
      Assert.Equal(2, counterExamples[0].Variables.Count);
      Assert.Equal(2, counterExamples[1].Variables.Count);
      Assert.True(counterExamples[0].Variables.ContainsKey("amount:int"));
      Assert.True(counterExamples[1].Variables.ContainsKey("amount:int"));
      Assert.True(counterExamples[0].Variables.ContainsKey("this:_module.BankAccountUnsafe"));
      Assert.True(counterExamples[1].Variables.ContainsKey("this:_module.BankAccountUnsafe"));
      StringAssert.Matches(counterExamples[0].Variables["this:_module.BankAccountUnsafe"], new Regex("\\(balance := [0-9]+\\)"));
      StringAssert.Matches(counterExamples[1].Variables["this:_module.BankAccountUnsafe"], new Regex("\\(balance := \\-[0-9]+\\)"));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task SpecificCharacter(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      method a(c:char) {
        assert c != '0';
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source, "SpecificCharacter.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.Equal(1, counterExamples[0].Variables.Count);
      Assert.True(counterExamples[0].Variables.ContainsKey("c:char"));
      Assert.Equal("'0'", counterExamples[0].Variables["c:char"]);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task ArbitraryCharacter(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      method a(c:char) {
        assert c == '0';
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source, "ArbitraryCharacter.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.Equal(1, counterExamples[0].Variables.Count);
      Assert.True(counterExamples[0].Variables.ContainsKey("c:char"));
      StringAssert.Matches(counterExamples[0].Variables["c:char"], new Regex("('.'|\\?#[0-9]+)"));
      Assert.NotEqual("'0'", counterExamples[0].Variables["c:char"]);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task DatatypeWithUnnamedDestructor(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      datatype B = A(int)
      method a(b:B) {
        assert b != A(5);
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source, "DatatypeWithUnnamedDestructor.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.Equal(1, counterExamples[0].Variables.Count);
      Assert.True(counterExamples[0].Variables.ContainsKey("b:_module.B"));
      // Unnamed destructors are implicitly assigned names starting with "#" during resolution:
      Assert.Equal("A(#0 := 5)", counterExamples[0].Variables["b:_module.B"]);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task DatatypeWithDestructorThanIsADataValue(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      datatype A = B(x:real)
      method destructorNameTest(a:A) {
        assert a.x >= 0.0 || a.x < -0.5;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source, "DatatypeWithDestructorThanIsADataValue.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.Equal(1, counterExamples[0].Variables.Count);
      Assert.True(counterExamples[0].Variables.ContainsKey("a:_module.A"));
      StringAssert.Matches(counterExamples[0].Variables["a:_module.A"], new Regex("B\\(x := -[0-9]+\\.[0-9]+/[0-9]+\\.[0-9]+\\)"));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task DatatypeWithDifferentDestructorsForDifferentConstructors(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      datatype Hand = Left(x:int, y:int) | Right(a:int, b:int)
      method T_datatype0_1(h0:Hand, h1:Hand)
        requires h0.Right? && h1.Left? {
        assert h0 == h1;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source, "DatatypeWithDifferentDestructorsForDifferentConstructors.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.Equal(2, counterExamples[0].Variables.Count);
      Assert.True(counterExamples[0].Variables.ContainsKey("h0:_module.Hand"));
      Assert.True(counterExamples[0].Variables.ContainsKey("h1:_module.Hand"));
      StringAssert.Matches(counterExamples[0].Variables["h0:_module.Hand"], new Regex("Right\\([a|b] := -?[0-9]+, [b|a] := -?[0-9]+\\)"));
      StringAssert.Matches(counterExamples[0].Variables["h1:_module.Hand"], new Regex("Left\\([x|y] := -?[0-9]+, [x|y] := -?[0-9]+\\)"));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task DatatypeObjectWithTwoDestructorsWhoseValuesAreEqual(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      datatype Hand = Left(a:int, b:int)
      method T_datatype0_1(h:Hand)  {
        assert h.a != h.b || h.a != 3;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source, "DatatypeObjectWithTwoDestructorsWhoseValuesAreEqual.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.Equal(1, counterExamples[0].Variables.Count);
      Assert.True(counterExamples[0].Variables.ContainsKey("h:_module.Hand"));
      StringAssert.Matches(counterExamples[0].Variables["h:_module.Hand"], new Regex("Left\\([a|b] := 3, [a|b] := 3\\)"));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task DatatypeWithDestructorsWhoseNamesShadowBuiltInDestructors(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      datatype A = B_(C_q:bool, B_q:bool, D_q:bool) | C(B_q:bool, C_q:bool, D_q:bool)
      method m (a:A) requires !a.B_?{
        assert a.C_q || a.B_q || a.D_q;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source, "DatatypeWithDestructorsWhoseNamesShadowBuiltInDestructors.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.Equal(1, counterExamples[0].Variables.Count);
      Assert.True(counterExamples[0].Variables.ContainsKey("a:_module.A"));
      StringAssert.Matches(counterExamples[0].Variables["a:_module.A"], new Regex("C\\((B_q|C_q|D_q) := false, (B_q|C_q|D_q) := false, (B_q|C_q|D_q) := false\\)"));
    }


    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task DatatypeWithTypeParameters(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      datatype A<T> = One(b:T) | Two(i:int)
      method m(a:A<bool>) requires a == One(false) || a == One(true) {
        assert a.b;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source, "DatatypeWithTypeParameters.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.Equal(1, counterExamples[0].Variables.Count);
      Assert.True(counterExamples[0].Variables.ContainsKey("a:_module.A<bool>"));
      Assert.Equal("One(b := false)", counterExamples[0].Variables["a:_module.A<bool>"]);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task ArbitraryBool(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      datatype List<T> = Nil | Cons(head: T, tail: List<T>)
      method listHasSingleElement(list:List<bool>)
        requires list != Nil
      {
        assert list.tail != Nil;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source, "ArbitraryBool.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.Equal(2, counterExamples[0].Variables.Count);
      Assert.True(counterExamples[0].Variables.ContainsKey("list:_module.List<bool>"));
      StringAssert.Matches(counterExamples[0].Variables["list:_module.List<bool>"], new Regex("Cons\\(head := (true|false), tail := @[0-9]+\\)"));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task ArbitraryInt(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      datatype List<T> = Nil | Cons(head: T, tail: List<T>)
      method listHasSingleElement(list:List<int>)
        requires list != Nil
      {
        assert list.tail != Nil;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source, "ArbitraryInt.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.Equal(2, counterExamples[0].Variables.Count);
      Assert.True(counterExamples[0].Variables.ContainsKey("list:_module.List<int>"));
      StringAssert.Matches(counterExamples[0].Variables["list:_module.List<int>"], new Regex("Cons\\(head := -?[0-9]+, tail := @[0-9]+\\)"));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task ArbitraryReal(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      datatype List<T> = Nil | Cons(head: T, tail: List<T>)
      method listHasSingleElement(list:List<real>)
        requires list != Nil
      {
        assert list.tail != Nil;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source, "ArbitraryReal.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.Equal(2, counterExamples[0].Variables.Count);
      Assert.True(counterExamples[0].Variables.ContainsKey("list:_module.List<real>"));
      StringAssert.Matches(counterExamples[0].Variables["list:_module.List<real>"], new Regex("Cons\\(head := -?[0-9]+\\.[0-9], tail := @[0-9]+\\)"));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task ArraySimpleTest(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      method a(arr:array<int>) requires arr.Length == 2 {
        assert arr[0] != 4 || arr[1] != 5;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source, "ArraySimpleTest.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.Equal(1, counterExamples[0].Variables.Count);
      Assert.True(counterExamples[0].Variables.ContainsKey("arr:_System.array<int>"), string.Join(", ", counterExamples[0].Variables));
      Assert.Equal("(Length := 2, [0] := 4, [1] := 5)", counterExamples[0].Variables["arr:_System.array<int>"]);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task SequenceSimpleTest(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      method a(s:seq<int>) requires |s| == 1 {
        assert s[0] != 4;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source, "SequenceSimpleTest.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.Equal(1, counterExamples[0].Variables.Count);
      Assert.True(counterExamples[0].Variables.ContainsKey("s:seq<int>"));
      Assert.Equal("[4]", counterExamples[0].Variables["s:seq<int>"]);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task SequenceOfBitVectors(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      method a(s:seq<bv5>) requires |s| == 2 {
        assert s[1] != (2 as bv5);
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source, "SequenceOfBitVectors.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.Equal(1, counterExamples[0].Variables.Count);
      Assert.True(counterExamples[0].Variables.ContainsKey("s:seq<bv5>"));
      Assert.Equal("(Length := 2, [1] := 2)", counterExamples[0].Variables["s:seq<bv5>"]);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task SpecificBitVector(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      method a(bv:bv7) {
        assert bv != (2 as bv7);
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source, "SpecificBitVector.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.Equal(1, counterExamples[0].Variables.Count);
      Assert.True(counterExamples[0].Variables.ContainsKey("bv:bv7"));
      Assert.Equal("2", counterExamples[0].Variables["bv:bv7"]);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task ArbitraryBitVector(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      method a(b:bv2) {
        assert b == (1 as bv2);
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source, "ArbitraryBitVector.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.Equal(1, counterExamples[0].Variables.Count);
      Assert.True(counterExamples[0].Variables.ContainsKey("b:bv2"));
      StringAssert.Matches(counterExamples[0].Variables["b:bv2"], new Regex("[023]"));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task BitWiseAnd(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      method m(a:bv1, b:bv1) {
        assert a & b != (1 as bv1);
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source, "BitWiseAnd.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.Equal(2, counterExamples[0].Variables.Count);
      Assert.True(counterExamples[0].Variables.ContainsKey("a:bv1"));
      Assert.True(counterExamples[0].Variables.ContainsKey("b:bv1"));
      StringAssert.Matches(counterExamples[0].Variables["a:bv1"], new Regex("(1|b)"));
      StringAssert.Matches(counterExamples[0].Variables["b:bv1"], new Regex("(1|a)"));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task BitVectorField(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      class Value {
        var b:bv5;
      }
      method a(v:Value) {
        assert v.b != (2 as bv5);
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source, "BitVectorField.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.Equal(1, counterExamples[0].Variables.Count);
      Assert.True(counterExamples[0].Variables.ContainsKey("v:_module.Value"));
      Assert.Equal("(b := 2)", counterExamples[0].Variables["v:_module.Value"]);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task SeqSetAndArrayAsTypeParameters(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      method a(s:set<seq<set<array<int>>>>) requires |s| <= 1{
        assert |s| == 0;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source, "SeqSetAndArrayAsTypeParameters.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.True(counterExamples[0].Variables.ContainsKey("s:set<seq<set<_System.array<int>>>>"));
      StringAssert.Matches(counterExamples[0].Variables["s:set<seq<set<_System.array<int>>>>"], new Regex("\\{@[0-9]+ := true\\}"));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task MultiDimensionalArray(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      method m(a:array3<int>) requires a.Length0 == 4 requires a.Length1 == 5 requires a.Length2 == 6 {
        assert a[2, 3, 1] != 7;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source, "MultiDimensionalArray.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.Equal(1, counterExamples[0].Variables.Count);
      Assert.True(counterExamples[0].Variables.ContainsKey("a:_System.array3<int>"), string.Join(", ", counterExamples[0].Variables));
      Assert.Equal("(Length0 := 4, Length1 := 5, Length2 := 6, [2,3,1] := 7)", counterExamples[0].Variables["a:_System.array3<int>"]);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task ArrayEqualityByReference(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      method test(x:array<int>, y:array<int>)   {
        assert x != y;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source, "ArrayEqualityByReference.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.Equal(2, counterExamples[0].Variables.Count);
      Assert.True(counterExamples[0].Variables.ContainsKey("x:_System.array<int>"));
      Assert.True(counterExamples[0].Variables.ContainsKey("y:_System.array<int>"));
      Assert.True(counterExamples[0].Variables["y:_System.array<int>"] == "x" || counterExamples[0].Variables["x:_System.array<int>"] == "y");
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task SetBasicOperations(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      method a(s1:set<char>, s2:set<char>) {
        var sUnion:set<char> := s1 + s2;
        var sInter:set<char> := s1 * s2;
        var sDiff:set<char> := s1 - s2;
        assert !('a' in sUnion) || ('a' in sInter) || !('b' in sInter) || !('a' in sDiff);
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source, "SetBasicOperations.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Equal(4, counterExamples.Length);
      Assert.Equal(5, counterExamples[2].Variables.Count);
      Assert.True(counterExamples[3].Variables.ContainsKey("s1:set<char>"));
      Assert.True(counterExamples[3].Variables.ContainsKey("s2:set<char>"));
      Assert.True(counterExamples[3].Variables.ContainsKey("sUnion:set<char>"));
      Assert.True(counterExamples[3].Variables.ContainsKey("sInter:set<char>"));
      Assert.True(counterExamples[3].Variables.ContainsKey("sDiff:set<char>"));
      var s1 = counterExamples[3].Variables["s1:set<char>"][1..^1].Split(", ");
      var s2 = counterExamples[3].Variables["s2:set<char>"][1..^1].Split(", ");
      var sUnion = counterExamples[3].Variables["sUnion:set<char>"][1..^1].Split(", ");
      var sInter = counterExamples[3].Variables["sInter:set<char>"][1..^1].Split(", ");
      var sDiff = counterExamples[3].Variables["sDiff:set<char>"][1..^1].Split(", ");
      Assert.Contains("'a' := true", s1);
      Assert.Contains("'a' := false", s2);
      Assert.Contains("'a' := true", sDiff);
      Assert.Contains("'a' := true", sUnion);
      Assert.Contains("'a' := false", sInter);
      Assert.Contains("'b' := true", s1);
      Assert.Contains("'b' := true", s2);
      Assert.Contains("'b' := false", sDiff);
      Assert.Contains("'b' := true", sUnion);
      Assert.Contains("'b' := true", sInter);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task SetSingleElement(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      method test() {
        var s := {6};
        assert 6 !in s;
      }".TrimStart();
      var documentItem = CreateTestDocument(source, "SetSingleElement.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Equal(2, counterExamples.Length);
      Assert.Equal(1, counterExamples[1].Variables.Count);
      Assert.True(counterExamples[1].Variables.ContainsKey("s:set<int>"));
      StringAssert.Matches(counterExamples[1].Variables["s:set<int>"], new Regex("\\{.*6 := true.*\\}"));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task StringBuilding(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = "" +
      "method a(s:string) {" +
      "  assert s != \"abc\";" +
      "  }".TrimStart();
      var documentItem = CreateTestDocument(source, "StringBuilding.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.Equal(1, counterExamples[0].Variables.Count);
      Assert.True(counterExamples[0].Variables.ContainsKey("s:seq<char>"));
      Assert.Equal("['a', 'b', 'c']", counterExamples[0].Variables["s:seq<char>"]);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task SequenceEdit(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = "" +
      "method a(c:char, s1:string) requires s1 == \"abc\"{" +
      "  var s2:string := s1[1 := c];" +
      "  assert s2[0] != 'a' || s2[1] !='d' || s2[2] != 'c';}".TrimStart();
      var documentItem = CreateTestDocument(source, "SequenceEdit.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Equal(2, counterExamples.Length);
      Assert.Equal(3, counterExamples[1].Variables.Count);
      Assert.True(counterExamples[1].Variables.ContainsKey("s1:seq<char>"));
      Assert.True(counterExamples[1].Variables.ContainsKey("s2:seq<char>"));
      Assert.True(counterExamples[1].Variables.ContainsKey("c:char"));
      Assert.Equal("['a', 'b', 'c']", counterExamples[1].Variables["s1:seq<char>"]);
      Assert.Equal("['a', 'd', 'c']", counterExamples[1].Variables["s2:seq<char>"]);
      Assert.Equal("'d'", counterExamples[1].Variables["c:char"]);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task SequenceSingleElement(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      method test() {
        var s := [6];
        assert 6 !in s;
      }".TrimStart();
      var documentItem = CreateTestDocument(source, "SequenceSingleElement.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Equal(2, counterExamples.Length);
      Assert.Equal(1, counterExamples[1].Variables.Count);
      Assert.True(counterExamples[1].Variables.ContainsKey("s:seq<int>"));
      StringAssert.Matches(counterExamples[1].Variables["s:seq<int>"], new Regex("\\[6\\]"));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task SequenceConcat(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      method a(s1:string, s2:string) requires |s1| == 1 && |s2| == 1 {
        var sCat:string := s2 + s1;
        assert sCat[0] != 'a' || sCat[1] != 'b';
      }".TrimStart();
      var documentItem = CreateTestDocument(source, "SequenceConcat.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Equal(2, counterExamples.Length);
      Assert.Equal(3, counterExamples[1].Variables.Count);
      Assert.True(counterExamples[1].Variables.ContainsKey("s1:seq<char>"));
      Assert.True(counterExamples[1].Variables.ContainsKey("s2:seq<char>"));
      Assert.True(counterExamples[1].Variables.ContainsKey("sCat:seq<char>"));
      Assert.Equal("['b']", counterExamples[1].Variables["s1:seq<char>"]);
      Assert.Equal("['a']", counterExamples[1].Variables["s2:seq<char>"]);
      Assert.Equal("['a', 'b']", counterExamples[1].Variables["sCat:seq<char>"]);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task SequenceGenerate(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      method a(multiplier:int) {
        var s:seq<int> := seq(3, i => i * multiplier);
        assert s[2] != 6;
      }".TrimStart();
      var documentItem = CreateTestDocument(source, "SequenceGenerate.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Equal(2, counterExamples.Length);
      Assert.True(counterExamples[1].Variables.ContainsKey("multiplier:int"));
      Assert.True(counterExamples[1].Variables.ContainsKey("s:seq<int>"));
      StringAssert.Matches(counterExamples[1].Variables["s:seq<int>"], new Regex("\\(Length := 3, .*\\[2\\] := 6.*\\)"));
      Assert.Equal("3", counterExamples[1].Variables["multiplier:int"]);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task SequenceSub(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      method a(s:seq<char>) requires |s| == 5 {
        var sSub:seq<char> := s[2..4];
        assert sSub[0] != 'a' || sSub[1] != 'b';
      }".TrimStart();
      var documentItem = CreateTestDocument(source, "SequenceSub.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Equal(2, counterExamples.Length);
      Assert.Equal(2, counterExamples[1].Variables.Count);
      Assert.True(counterExamples[1].Variables.ContainsKey("sSub:seq<char>"));
      Assert.True(counterExamples[1].Variables.ContainsKey("s:seq<char>"));
      Assert.Equal("['a', 'b']", counterExamples[1].Variables["sSub:seq<char>"]);
      StringAssert.Matches(counterExamples[0].Variables["s:seq<char>"], new Regex("\\(Length := 5,.*\\[2\\] := 'a', \\[3\\] := 'b'.*"));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task SequenceDrop(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      method a(s:seq<char>) requires |s| == 5 {
        var sSub:seq<char> := s[2..];
        assert sSub[0] != 'a' || sSub[1] != 'b' || sSub[2] != 'c';
      }".TrimStart();
      var documentItem = CreateTestDocument(source, "SequenceDrop.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Equal(2, counterExamples.Length);
      Assert.Equal(2, counterExamples[1].Variables.Count);
      Assert.True(counterExamples[1].Variables.ContainsKey("sSub:seq<char>"));
      Assert.True(counterExamples[1].Variables.ContainsKey("s:seq<char>"));
      Assert.Equal("['a', 'b', 'c']", counterExamples[1].Variables["sSub:seq<char>"]);
      StringAssert.Matches(counterExamples[0].Variables["s:seq<char>"], new Regex("\\(Length := 5,.*\\[2\\] := 'a', \\[3\\] := 'b', \\[4\\] := 'c'.*"));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task SequenceTake(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      method a(s:seq<char>) requires |s| == 5 {
        var sSub:seq<char> := s[..3];
        assert sSub[0] != 'a' || sSub[1] != 'b' || sSub[2] != 'c';
      }".TrimStart();
      var documentItem = CreateTestDocument(source, "SequenceTake.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Equal(2, counterExamples.Length);
      Assert.Equal(2, counterExamples[1].Variables.Count);
      Assert.True(counterExamples[1].Variables.ContainsKey("sSub:seq<char>"));
      Assert.True(counterExamples[1].Variables.ContainsKey("s:seq<char>"));
      Assert.Equal("['a', 'b', 'c']", counterExamples[1].Variables["sSub:seq<char>"]);
      StringAssert.Matches(counterExamples[0].Variables["s:seq<char>"], new Regex("\\(Length := 5,.*\\[0\\] := 'a', \\[1\\] := 'b', \\[2\\] := 'c'.*"));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task VariableNameShadowing(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      method test(m:set<int>) {
        var m := {6};
        assert 6 !in m;
      }".TrimStart();
      var documentItem = CreateTestDocument(source, "VariableNameShadowing.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Equal(2, counterExamples.Length);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task MapsCreation(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      method test() {
        var m := map[3 := false];
        assert m[3];
      }".TrimStart();
      var documentItem = CreateTestDocument(source, "MapsCreation.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Equal(2, counterExamples.Length);
      Assert.Equal(1, counterExamples[1].Variables.Count);
      Assert.True(counterExamples[1].Variables.ContainsKey("m:map<int, bool>"));
      StringAssert.Matches(counterExamples[1].Variables["m:map<int, bool>"], new Regex("map\\[.*3 := false.*"));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task MapsEmpty(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      method test() {
        var m : map<int,int> := map[];
        assert 3 in m;
      }".TrimStart();
      var documentItem = CreateTestDocument(source, "MapsEmpty.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Equal(2, counterExamples.Length);
      Assert.Equal(1, counterExamples[1].Variables.Count);
      Assert.True(counterExamples[1].Variables.ContainsKey("m:map<int, int>"));
      Assert.Equal("map[]", counterExamples[1].Variables["m:map<int, int>"]);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task TraitType(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      module M {
        trait C {
          predicate Valid() {false}
        }
        method test(c:C) {
          assert c.Valid();
        }
      }".TrimStart();
      var documentItem = CreateTestDocument(source, "TraitType.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.Single(counterExamples[0].Variables);
      Assert.True(counterExamples[0].Variables.ContainsKey("c:M.C"));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task ArrowType(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      module M {
        method test() {
          var c: (int, bool) ~> real;
          var x := c(1, false);
          assert x == 2.4;
        }
      }".TrimStart();
      var documentItem = CreateTestDocument(source, "ArrowType.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.True(counterExamples[^1].Variables.ContainsKey("c:(int, bool) ~> real"));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task MapAsTypeArgument(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      method test() {
        var s : set<map<int,int>> := {map[3:=5]};
        assert |s| == 0;
      }".TrimStart();
      var documentItem = CreateTestDocument(source, "MapAsTypeArgument.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Equal(2, counterExamples.Length);
      Assert.Equal(2, counterExamples[1].Variables.Count);
      Assert.True(counterExamples[1].Variables.ContainsKey("s:set<map<int, int>>"));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task DatatypeTypeAsTypeArgument(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      module M {
        datatype C = A | B
        method test() {
          var s : set<C> := {A};
          assert |s| == 0;
        }
      }".TrimStart();
      var documentItem = CreateTestDocument(source, "DatatypeTypeAsTypeArgument.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Equal(2, counterExamples.Length);
      Assert.Equal(2, counterExamples[1].Variables.Count);
      Assert.True(counterExamples[1].Variables.ContainsKey("s:set<M.C>"));
      Assert.Contains(counterExamples[1].Variables.Keys, key => key.EndsWith("M.C"));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task SetsEmpty(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      method test() {
        var s : set<int> := {};
        assert false;
      }".TrimStart();
      var documentItem = CreateTestDocument(source, "SetsEmpty.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Equal(2, counterExamples.Length);
      Assert.Equal(1, counterExamples[1].Variables.Count);
      // Cannot infer the type when Arguments polymorphic encoding is used
      Assert.True(counterExamples[1].Variables.ContainsKey("s:set<?>"));
      Assert.Equal("{}", counterExamples[1].Variables["s:set<?>"]);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task MapsUpdate(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      method test(value:int) {
        var m := map[3 := -1];
        var b := m[3] == -1;
        m := m[3 := value];
        assert b && m[3] <= 0;
      }".TrimStart();
      var documentItem = CreateTestDocument(source, "MapsUpdate.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Equal(4, counterExamples.Length);
      Assert.Equal(2, counterExamples[1].Variables.Count);
      Assert.True(counterExamples[1].Variables.ContainsKey("m:map<int, int>"));
      StringAssert.Matches(counterExamples[1].Variables["m:map<int, int>"], new Regex("map\\[.*3 := -1.*"));
      Assert.Equal(3, counterExamples[3].Variables.Count);
      Assert.True(counterExamples[3].Variables.ContainsKey("m:map<int, int>"));
      Assert.True(counterExamples[3].Variables.ContainsKey("value:int"));
      Assert.True(counterExamples[3].Variables.ContainsKey("b:bool"));
      Assert.Equal("true", counterExamples[3].Variables["b:bool"]);
      StringAssert.Matches(counterExamples[3].Variables["value:int"], new Regex("[1-9][0-9]*"));
      StringAssert.Matches(counterExamples[3].Variables["m:map<int, int>"], new Regex("map\\[.*3 := [1-9].*"));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task MapsUpdateStoredInANewVariable(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      method T_map1(m:map<int,int>, key:int, val:int)
        requires key in m.Keys
      {
        var m' := m[key := val - 1];
        m' := m'[key := val];
        assert m'.Values == m.Values - {m[key]} + {val};
      }".TrimStart();
      var documentItem = CreateTestDocument(source, "MapsUpdateStoredInANewVariable.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Equal(3, counterExamples.Length);
      Assert.Equal(4, counterExamples[2].Variables.Count);
      Assert.True(counterExamples[2].Variables.ContainsKey("m:map<int, int>"));
      Assert.True(counterExamples[2].Variables.ContainsKey("m':map<int, int>"));
      Assert.True(counterExamples[2].Variables.ContainsKey("val:int"));
      Assert.True(counterExamples[2].Variables.ContainsKey("key:int"));
      var key = counterExamples[2].Variables["key:int"];
      var val = counterExamples[2].Variables["val:int"];
      StringAssert.Matches(counterExamples[2].Variables["m':map<int, int>"], new Regex("map\\[.*" + key + " := " + val + ".*"));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task MapsBuildRecursive(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      method T_map2()
      {
        var m := map[5 := 39];
        m := m[5 := 38];
        m := m[5 := 37];
        m := m[5 := 36];
        assert 5 !in m;
      }".TrimStart();
      var documentItem = CreateTestDocument(source, "MapsBuildRecursive.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Equal(5, counterExamples.Length);
      Assert.Equal(1, counterExamples[4].Variables.Count);
      Assert.True(counterExamples[4].Variables.ContainsKey("m:map<int, int>"));
      StringAssert.Matches(counterExamples[4].Variables["m:map<int, int>"], new Regex("map\\[.*5 := 36.*"));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task MapsValuesUpdate(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      // This corner case previously triggered infinite loops
      var source = @"
      method T_map0(m:map<int,int>, key:int, val:int)
      {
        var m' := m[key := val];
        assert m.Values + {val} == m'.Values;
      }".TrimStart();
      var documentItem = CreateTestDocument(source, "MapsValuesUpdate.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Equal(2, counterExamples.Length);
      Assert.Equal(4, counterExamples[1].Variables.Count);
      Assert.True(counterExamples[1].Variables.ContainsKey("m:map<int, int>"));
      Assert.True(counterExamples[1].Variables.ContainsKey("m':map<int, int>"));
      Assert.True(counterExamples[1].Variables.ContainsKey("val:int"));
      Assert.True(counterExamples[1].Variables.ContainsKey("key:int"));
      var key = counterExamples[1].Variables["key:int"];
      var val = counterExamples[1].Variables["val:int"];
      var mapRegex = new Regex("map\\[.*" + key + " := " + val + ".*");
      Assert.True(mapRegex.IsMatch(counterExamples[1].Variables["m':map<int, int>"]) ||
                    mapRegex.IsMatch(counterExamples[1].Variables["m:map<int, int>"]));

    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task MapsKeys(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      method test(m:map<int,char>) {
        var keys := m.Keys;
        assert (25 !in keys);
      }".TrimStart();
      var documentItem = CreateTestDocument(source, "MapsKeys.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Equal(2, counterExamples.Length);
      Assert.Equal(2, counterExamples[1].Variables.Count);
      Assert.True(counterExamples[1].Variables.ContainsKey("m:map<int, char>"));
      Assert.True(counterExamples[1].Variables.ContainsKey("keys:set<int>"));
      StringAssert.Matches(counterExamples[1].Variables["m:map<int, char>"], new Regex("map\\[.*25 := .*"));
      StringAssert.Matches(counterExamples[1].Variables["keys:set<int>"], new Regex("\\{.*25 := true.*"));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task MapsValues(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      method test(m:map<int,char>) {
        var values := m.Values;
        assert ('c' !in values);
      }".TrimStart();
      var documentItem = CreateTestDocument(source, "MapsValues.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Equal(2, counterExamples.Length);
      Assert.Equal(2, counterExamples[1].Variables.Count);
      Assert.True(counterExamples[1].Variables.ContainsKey("m:map<int, char>"));
      Assert.True(counterExamples[1].Variables.ContainsKey("values:set<char>"));
      StringAssert.Matches(counterExamples[1].Variables["m:map<int, char>"], new Regex("map\\[.* := 'c'.*"));
      StringAssert.Matches(counterExamples[1].Variables["values:set<char>"], new Regex("\\{.*'c' := true.*"));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task MapsOfBitVectors(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      // This test case triggers a situation in which the model does not
      // specify concrete values for bit vectors and the counterexample extraction
      // tool has to come up with such a value
      var source = @"
      method test(m:map<bv2,bv3>) {
        assert |m| == 0;
      }".TrimStart();
      var documentItem = CreateTestDocument(source, "MapsOfBitVectors.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.Equal(1, counterExamples[0].Variables.Count);
      Assert.True(counterExamples[0].Variables.ContainsKey("m:map<bv2, bv3>"));
      StringAssert.Matches(counterExamples[0].Variables["m:map<bv2, bv3>"], new Regex("map\\[.*[0-9]+ := [0-9]+.*"));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task ModuleRenaming(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
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
      var documentItem = CreateTestDocument(source, "ModuleRenaming.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.Equal(1, counterExamples[0].Variables.Count);
      Assert.True(counterExamples[0].Variables.ContainsKey("this:Mo_dule_.Module2_.Cla__ss"));
      Assert.Equal("(i := 5)", counterExamples[0].Variables["this:Mo_dule_.Module2_.Cla__ss"]);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task UnboundedIntegers(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      ghost const NAT64_MAX := 0x7fff_ffff_ffff_ffff

      newtype nat64 = x | 0 <= x <= NAT64_MAX

      function plus(a: nat64, b: nat64): nat64 {
        a + b
      }".TrimStart();
      var documentItem = CreateTestDocument(source, "UnboundedIntegers.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.True(counterExamples[0].Variables.ContainsKey("a:int"));
      Assert.True(counterExamples[0].Variables.ContainsKey("b:int"));
      var a = long.Parse(counterExamples[0].Variables["a:int"]);
      var b = long.Parse(counterExamples[0].Variables["b:int"]);
      Assert.True(a + b < a || a + b < b);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task DatatypeWithPredicate(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
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
      var documentItem = CreateTestDocument(source, "DatatypeWithPredicate.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.True(counterExamples[0].Variables.ContainsKey("d:M.D"));
      Assert.Equal("C(i := 123)", counterExamples[0].Variables["d:M.D"]);
    }

    /** Makes sure the counterexample lists the base type of a variable */
    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task SubsetType(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = "" +
      "type String = s:string | |s| > 0 witness \"a\"" +
      "method a(s:String) {" +
      "  assert s != \"aws\";" +
      "}".TrimStart();
      var documentItem = CreateTestDocument(source, "SubsetType.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.True(counterExamples[0].Variables.ContainsKey("s:seq<char>"));
      Assert.Equal("['a', 'w', 's']", counterExamples[0].Variables["s:seq<char>"]);
    }

    /// <summary>
    /// Test a situation in which two fields of an object are equal
    /// (the value is represented by one Element in the Model)
    /// </summary>
    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task EqualFields(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      module M {
        class C { 
          var c1:char;
          var c2:char;
        }

        method test(c: C?) {
          assert c == null || c.c1 != c.c2 || c.c1 != '\U{1023}';
        }
      }".TrimStart();
      var documentItem = CreateTestDocument(source, "EqualFields.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.True(counterExamples[0].Variables.ContainsKey("c:M.C?"));
      Assert.True(counterExamples[0].Variables["c:M.C?"] is
        "(c1 := '\\u1023', c2 := '\\u1023')" or
        "(c2 := '\\u1023', c1 := '\\u1023')");
    }

    /// <summary>
    /// Tests that a Dafny program where a sequence with non-integral indices is generated as part of
    /// a counterexample.  This would previously crash the LSP before #3093.
    /// For more details, see https://github.com/dafny-lang/dafny/issues/3048 .
    /// </summary>
    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task NonIntegerSeqIndices(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      string fp = Path.Combine(Directory.GetCurrentDirectory(), "Various", "TestFiles", "3048.dfy");
      var source = await File.ReadAllTextAsync(fp, CancellationToken);
      var documentItem = CreateTestDocument(source, "NonIntegerSeqIndices.dfy");

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
      Assert.True(nonIntegralIndexedSeqs > 0, "If we do not see at least one non-integral index in " +
                                                "this test case, then the backend changed " +
                                                "The indices being returned to the Language Server.");
                                                */
    }

    /* Helper for the NonIntegerSeqIndices test. */
    private static bool IsNegativeIndexedSeq(KeyValuePair<string, string> kvp) {
      var r = new Regex(@"\[\(- \d+\)\]");
      return kvp.Key.Contains("seq<_module.uint8>") && r.IsMatch(kvp.Value);
    }

    [Fact]
    public void TestIsNegativeIndexedSeq() {
      Assert.False(
        IsNegativeIndexedSeq(new KeyValuePair<string, string>("uint8", "42")));
      Assert.False(
        IsNegativeIndexedSeq(new KeyValuePair<string, string>("seq<_module.uint8>", "(Length := 42, [0] := 42)")));
      Assert.True(
        IsNegativeIndexedSeq(new KeyValuePair<string, string>("seq<_module.uint8>", "(Length := 9899, [(- 1)] := 42)")));
      Assert.True(
        IsNegativeIndexedSeq(new KeyValuePair<string, string>("seq<seq<_module.uint8>>", "(Length := 1123, [(- 12345)] := @12)")));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task TypePolymorphism(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      module M { 
        class C<T> {
          function Equal<T> (a:T, b:T):bool { assert a != b; true }
        }
      }".TrimStart();
      var documentItem = CreateTestDocument(source, "TypePolymorphism.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.Equal(3, counterExamples[0].Variables.Count);
      Assert.True(counterExamples[0].Variables.ContainsKey("a:M.C.Equal$T"));
      Assert.True(counterExamples[0].Variables.ContainsKey("b:M.C.Equal$T"));
      Assert.True(counterExamples[0].Variables.ContainsKey("this:M.C<M.C$T>"));
    }

    /// <summary>
    /// This test case would previously lead to stack overflow because of infinite recursion in GetDafnyType
    /// </summary>
    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task GetDafnyTypeInfiniteRecursion(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      class Seq {
        var s:seq<int>
        method test(i0:nat, val0:int, i1:nat, val1:int) 
          modifies this {
          assume 0 <= i0 < i1 < |s|;
          s := s[i0 := val0];
          s := s[i1 := val1];
          assert s[0] != 0;
        }
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source, "GetDafnyTypeInfiniteRecursion.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      (await RequestCounterExamples(documentItem.Uri)).ToList();
    }

    public CounterExampleTest(ITestOutputHelper output) : base(output) {
    }
  }
}