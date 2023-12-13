using System;
using System.Collections.Generic;
using System.IO;
using Microsoft.Dafny.LanguageServer.Handlers.Custom;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using OmniSharp.Extensions.LanguageServer.Protocol;
using System.Linq;
using System.Numerics;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Workspace;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various {

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
      Assert.Contains("y is int", counterExamples[0].Assumption);
      var regex = new Regex("y == (-?[0-9]+);");
      Assert.Matches(regex, counterExamples[0].Assumption);
      var y = BigInteger.Parse(regex.Match(counterExamples[0].Assumption).Groups[1].Value);
      Assert.True(y.CompareTo(BigInteger.Zero) <= 0);
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
      Assert.Contains("y is int", counterExamples[0].Assumption);
      var regex = new Regex("y == (-?[0-9]+)");
      Assert.Matches(regex, counterExamples[0].Assumption);
      var y = BigInteger.Parse(regex.Match(counterExamples[0].Assumption).Groups[1].Value);
      Assert.True(y.CompareTo(BigInteger.Zero) <= 0);
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
      Assert.Matches(new Regex("[xyz] is int"), counterExamples[2].Assumption);
      Assert.Matches(new Regex("[xyz] == -[0-9]+"), counterExamples[2].Assumption);
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
        ensures y >= 0
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
      Assert.Contains("y is int", counterExamples[0].Assumption);
      Assert.Matches(new Regex("y == -[0-9]+"), counterExamples[0].Assumption);
      Assert.Equal((7, 6), counterExamples[1].Position);
      Assert.Contains("a is int", counterExamples[1].Assumption);
      Assert.Contains("b is int", counterExamples[1].Assumption);
      var aRegex = new Regex("a == (-?[0-9]+)");
      var bRegex = new Regex("b == (-?[0-9]+)");
      Assert.Matches(aRegex, counterExamples[1].Assumption);
      Assert.Matches(bRegex, counterExamples[1].Assumption);
      Assert.NotEqual(
        aRegex.Match(counterExamples[1].Assumption).Groups[1].Value,
        bRegex.Match(counterExamples[1].Assumption).Groups[1].Value);
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
      Assert.Contains("r is real", counterExamples[0].Assumption);
      Assert.Contains("r == 1.0", counterExamples[0].Assumption);
    }
    
    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task SpecificInteger(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      method a(i:int) {
        assert i != 25;
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source, "integer.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.Contains("i is int", counterExamples[0].Assumption);
      Assert.Contains("i == 25", counterExamples[0].Assumption);
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
      Assert.Contains("r is real", counterExamples[0].Assumption);
      Assert.Matches(new Regex("r == [0-9]+\\.[0-9]+ / [0-9]+\\.[0-9]+;"), counterExamples[0].Assumption);
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
      Assert.Fail("This test needs to be updated");
      // Assert.Equal(1, counterExamples[0].Variables.Count);
      // Assert.True(counterExamples[0].Variables.ContainsKey("v:_module.Value"));
      // Assert.Equal("(v := 0.0)", counterExamples[0].Variables["v:_module.Value"]);
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
      Assert.Contains("v is Value", counterExamples[0].Assumption);
      Assert.Matches("(v.with_underscore_|42) is int", counterExamples[0].Assumption);
      Assert.Matches("(v.with_underscore_ == 42|42 == v.with_underscore_)", counterExamples[0].Assumption);
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
      Assert.Fail("This test needs to be updated");
      // Assert.Equal(1, counterExamples[0].Variables.Count);
      // Assert.True(counterExamples[0].Variables.ContainsKey("v:_module.Value"));
      // StringAssert.Matches(counterExamples[0].Variables["v:_module.Value"], new Regex("\\(v := [0-9]+\\.[0-9]+/[0-9]+\\.[0-9]+\\)"));
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
      Assert.Fail("This test needs to be updated");
      // Assert.Equal(1, counterExamples[0].Variables.Count);
      // Assert.True(counterExamples[0].Variables.ContainsKey("n:_module.Node"));
      // Assert.Equal("(next := n)", counterExamples[0].Variables["n:_module.Node"]);
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
      Assert.Fail("This test needs to be updated");
      // Assert.Equal(2, counterExamples[0].Variables.Count);
      // Assert.True(counterExamples[0].Variables.ContainsKey("n:_module.Node"));
      // StringAssert.Matches(counterExamples[0].Variables["n:_module.Node"], new Regex("\\(next := @[0-9]+\\)"));
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
      Assert.Fail("This test needs to be updated");
      // Assert.Equal(1, counterExamples[0].Variables.Count);
      // Assert.True(counterExamples[0].Variables.ContainsKey("n:_module.Node"));
      // Assert.Equal("(next := null)", counterExamples[0].Variables["n:_module.Node"]);
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
      Assert.Fail("This test needs to be updated");
      // Assert.Equal(2, counterExamples[0].Variables.Count);
      // Assert.Equal(2, counterExamples[1].Variables.Count);
      // Assert.True(counterExamples[0].Variables.ContainsKey("amount:int"));
      // Assert.True(counterExamples[1].Variables.ContainsKey("amount:int"));
      // Assert.True(counterExamples[0].Variables.ContainsKey("this:_module.BankAccountUnsafe"));
      // Assert.True(counterExamples[1].Variables.ContainsKey("this:_module.BankAccountUnsafe"));
      // StringAssert.Matches(counterExamples[0].Variables["this:_module.BankAccountUnsafe"], new Regex("\\(balance := [0-9]+\\)"));
      // StringAssert.Matches(counterExamples[1].Variables["this:_module.BankAccountUnsafe"], new Regex("\\(balance := \\-[0-9]+\\)"));
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
      Assert.Contains("c is char", counterExamples[0].Assumption);
      Assert.Contains("c == '0'", counterExamples[0].Assumption);
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
      Assert.Contains("c is char", counterExamples[0].Assumption);
      Assert.Contains("c != '0'", counterExamples[0].Assumption);
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
      Assert.Contains("b is B", counterExamples[0].Assumption);
      Assert.Contains("b == B.A(5)", counterExamples[0].Assumption);
    }
    
    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task DatatypeWithUnnamedDestructor2(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      datatype A = A(i:int)
      datatype B = B(A)
      method a(b:B) {
        assert b != B(A(5));
      }
      ".TrimStart();
      var documentItem = CreateTestDocument(source, "DatatypeWithUnnamedDestructor.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.Contains("exists boundVar0: A ::", counterExamples[0].Assumption);
      Assert.Contains("b is B", counterExamples[0].Assumption);
      Assert.Contains("b == B.B(boundVar0)", counterExamples[0].Assumption);
      Assert.Contains("boundVar0 is A", counterExamples[0].Assumption);
      Assert.Contains("boundVar0.A?", counterExamples[0].Assumption);
      Assert.Matches(new Regex("(boundVar0.i|5) is int"), counterExamples[0].Assumption);
      Assert.Matches(new Regex("(boundVar0.i|5) == (boundVar0.i|5)"), counterExamples[0].Assumption);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task DatatypeWithDestructorThatIsADataValue(Action<DafnyOptions> optionSettings) {
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
      Assert.Contains("a is A", counterExamples[0].Assumption);
      Assert.Contains("a.B?", counterExamples[0].Assumption);
      Assert.Contains("a.x is real", counterExamples[0].Assumption);
      Assert.Matches(new Regex("a.x == -\\(?[0-9]+\\.[0-9]+ / [0-9]+\\.[0-9]+"), counterExamples[0].Assumption);
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
      Assert.Contains("h0 is Hand", counterExamples[0].Assumption);
      Assert.Contains("h1 is Hand", counterExamples[0].Assumption);
      Assert.Contains("h0.Right?", counterExamples[0].Assumption);
      Assert.Contains("h1.Left?", counterExamples[0].Assumption);
      Assert.Contains("h0.a is int", counterExamples[0].Assumption);
      Assert.Contains("h0.b is int", counterExamples[0].Assumption);
      Assert.Contains("h1.x is int", counterExamples[0].Assumption);
      Assert.Contains("h1.y is int", counterExamples[0].Assumption);
      Assert.DoesNotContain("h1.a", counterExamples[0].Assumption);
      Assert.DoesNotContain("h1.b", counterExamples[0].Assumption);
      Assert.DoesNotContain("h0.x", counterExamples[0].Assumption);
      Assert.DoesNotContain("h0.y", counterExamples[0].Assumption);
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
      Assert.Contains("h is Hand", counterExamples[0].Assumption);
      Assert.Contains("h.Left?", counterExamples[0].Assumption);
      Assert.Matches(new Regex("h.[ab] is int"), counterExamples[0].Assumption);
      Assert.Matches(new Regex("h.[ab] == 3"), counterExamples[0].Assumption);
      Assert.Matches(new Regex("h.[ab] == h.[ab]"), counterExamples[0].Assumption);
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
      Assert.Contains("a is A", counterExamples[0].Assumption);
      Assert.Contains("a.C?", counterExamples[0].Assumption);
      Assert.Matches(new Regex("a.[BCD]_q is bool"), counterExamples[0].Assumption);
      Assert.Matches(new Regex("a.[BCD]_q == false"), counterExamples[0].Assumption);
      Assert.DoesNotContain("true", counterExamples[0].Assumption);
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
      Assert.Contains("a is A<bool>", counterExamples[0].Assumption);
      Assert.Contains("a.One?", counterExamples[0].Assumption);
      Assert.Contains("a.b is bool", counterExamples[0].Assumption);
      Assert.Contains("a.b == false", counterExamples[0].Assumption);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task DestructorDoesNotMatterBoolean(Action<DafnyOptions> optionSettings) {
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
      Assert.Contains("list is List<bool>", counterExamples[0].Assumption);
      Assert.Contains("list.Cons?", counterExamples[0].Assumption);
      Assert.Contains("list.tail is List<bool>", counterExamples[0].Assumption);
      Assert.Contains("list.tail.Nil?", counterExamples[0].Assumption);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task DestructorDoesNotMatter(Action<DafnyOptions> optionSettings) {
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
      Assert.Contains("list is List<int>", counterExamples[0].Assumption);
      Assert.Contains("list.Cons?", counterExamples[0].Assumption);
      Assert.Contains("list.tail is List<int>", counterExamples[0].Assumption);
      Assert.Contains("list.tail.Nil?", counterExamples[0].Assumption);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task DestructorDoesNotReal(Action<DafnyOptions> optionSettings) {
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
      Assert.Contains("list is List<real>", counterExamples[0].Assumption);
      Assert.Contains("list.Cons?", counterExamples[0].Assumption);
      Assert.Contains("list.tail is List<real>", counterExamples[0].Assumption);
      Assert.Contains("list.tail.Nil?", counterExamples[0].Assumption);
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
      Assert.Contains("arr is array<int>", counterExamples[0].Assumption);
      Assert.Contains("arr.Length == 2", counterExamples[0].Assumption);
      Assert.Contains("arr[0] == 4", counterExamples[0].Assumption);
      Assert.Contains("arr[1] == 5", counterExamples[0].Assumption);
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
      Assert.Contains("s is seq<int>", counterExamples[0].Assumption);
      Assert.Contains("|s| == 1", counterExamples[0].Assumption);
      Assert.Matches(new Regex("(s\\[0\\]|4) == (s\\[0\\]|4)"), counterExamples[0].Assumption);
      Assert.Matches(new Regex("(s\\[0\\]|4) is int"), counterExamples[0].Assumption);
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
      Assert.Contains("s is seq<bv5>", counterExamples[0].Assumption);
      Assert.Contains("|s| == 2", counterExamples[0].Assumption);
      Assert.Matches(new Regex("(s\\[1\\]|2) == (s\\[1\\]|2)"), counterExamples[0].Assumption);
      Assert.Matches(new Regex("(s\\[1\\]|2) is bv5"), counterExamples[0].Assumption);
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
      Assert.Contains("bv is bv7", counterExamples[0].Assumption);
      Assert.Contains("bv == 2", counterExamples[0].Assumption);
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
      Assert.Contains("b is bv2", counterExamples[0].Assumption);
      Assert.Matches(new Regex("b == [023]"), counterExamples[0].Assumption);
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
      Assert.Matches(new Regex("[ab] is bv1"), counterExamples[0].Assumption);
      Assert.Matches(new Regex("[ab] == (1|b)"), counterExamples[0].Assumption);
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
      Assert.Contains("v is Value", counterExamples[0].Assumption);
      Assert.Matches("(v.b|2) is bv5", counterExamples[0].Assumption);
      Assert.Matches("(v.b == 2|2 == v.b)", counterExamples[0].Assumption);
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
      Assert.Fail("This test needs to be updated");
      // Assert.True(counterExamples[0].Variables.ContainsKey("s:set<seq<set<_System.array<int>>>>"));
      // StringAssert.Matches(counterExamples[0].Variables["s:set<seq<set<_System.array<int>>>>"], new Regex("\\{@[0-9]+ := true\\}"));
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
      Assert.Fail("This test needs to be updated");
      // Assert.Equal(1, counterExamples[0].Variables.Count);
      // Assert.True(counterExamples[0].Variables.ContainsKey("a:_System.array3<int>"), string.Join(", ", counterExamples[0].Variables));
      // Assert.Equal("(Length0 := 4, Length1 := 5, Length2 := 6, [2,3,1] := 7)", counterExamples[0].Variables["a:_System.array3<int>"]);
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
      Assert.Matches(new Regex("[xy] is array<int>"), counterExamples[0].Assumption);
      Assert.Matches(new Regex("(x == y|y == x)"), counterExamples[0].Assumption);
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
      Assert.Contains("s1 is set<char>", counterExamples[3].Assumption);
      Assert.Contains("s2 is set<char>", counterExamples[3].Assumption);
      Assert.Contains("sInter is set<char>", counterExamples[3].Assumption);
      Assert.Contains("sUnion is set<char>", counterExamples[3].Assumption);
      Assert.Contains("sDiff is set<char>", counterExamples[3].Assumption);
      Assert.Contains("'a' in s1", counterExamples[3].Assumption);
      Assert.Contains("'a' !in s2", counterExamples[3].Assumption);
      Assert.Contains("'a' in sDiff", counterExamples[3].Assumption);
      Assert.Contains("'a' in sUnion", counterExamples[3].Assumption);
      Assert.Contains("'a' !in sInter", counterExamples[3].Assumption);
      Assert.Contains("'b' in s1", counterExamples[3].Assumption);
      Assert.Contains("'b' in s2", counterExamples[3].Assumption);
      Assert.Contains("'b' !in sDiff", counterExamples[3].Assumption);
      Assert.Contains("'b' in sUnion", counterExamples[3].Assumption);
      Assert.Contains("'b' in sInter", counterExamples[3].Assumption);
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
      Assert.Contains("s is set<int>", counterExamples[1].Assumption);
      Assert.Contains("6 in s", counterExamples[1].Assumption);
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
      Assert.Contains("s is seq<char>", counterExamples[0].Assumption);
      Assert.Contains("s[0] == 'a'", counterExamples[0].Assumption);
      Assert.Contains("s[1] == 'b'", counterExamples[0].Assumption);
      Assert.Contains("s[2] == 'c'", counterExamples[0].Assumption);
      Assert.Contains("|s| == 3", counterExamples[0].Assumption);
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
      Assert.Contains("s2 is seq<char>", counterExamples[1].Assumption);
      Assert.Matches(new Regex("('a'|s1\\[0\\]) == s2\\[0\\]"), counterExamples[1].Assumption);
      Assert.Matches(new Regex("('d'|c) == s2\\[1\\]"), counterExamples[1].Assumption);
      Assert.Matches(new Regex("('c'|s1\\[2\\]) == s2\\[2\\]"), counterExamples[1].Assumption);
      Assert.Contains("|s2| == 3", counterExamples[1].Assumption);
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
      Assert.Contains("s is seq<int>", counterExamples[1].Assumption);
      Assert.Contains("|s| == 1", counterExamples[1].Assumption);
      Assert.Matches(new Regex("(s\\[0\\]|6) == (s\\[0\\]|6)"), counterExamples[1].Assumption);
      Assert.Matches(new Regex("(s\\[0\\]|6) is int"), counterExamples[1].Assumption);
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
      Assert.Contains("s1 is seq<char>", counterExamples[1].Assumption);
      Assert.Contains("s2 is seq<char>", counterExamples[1].Assumption);
      Assert.Contains("sCat is seq<char>", counterExamples[1].Assumption);
      Assert.Contains("sCat[1] == s1[0]", counterExamples[1].Assumption);
      Assert.Contains("sCat[0] == s2[0]", counterExamples[1].Assumption);
      Assert.Contains("sCat[0] == 'a'", counterExamples[1].Assumption);
      Assert.Contains("sCat[1] == 'b'", counterExamples[1].Assumption);
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
      Assert.Fail("This test needs to be updated");
      Assert.Equal(2, counterExamples.Length);
      // Assert.True(counterExamples[1].Variables.ContainsKey("multiplier:int"));
      // Assert.True(counterExamples[1].Variables.ContainsKey("s:seq<int>"));
      // StringAssert.Matches(counterExamples[1].Variables["s:seq<int>"], new Regex("\\(Length := 3, .*\\[2\\] := 6.*\\)"));
      // Assert.Equal("3", counterExamples[1].Variables["multiplier:int"]);
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
      Assert.Contains("sSub is seq<char>", counterExamples[1].Assumption);
      Assert.Matches(new Regex("('a'|s\\[2\\]) == sSub\\[0\\]"), counterExamples[1].Assumption);
      Assert.Matches(new Regex("('b'|s\\[3\\]) == sSub\\[1\\]"), counterExamples[1].Assumption);
      Assert.Contains("|sSub| == 2", counterExamples[1].Assumption);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task SequenceDrop(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      method a(s:seq<char>) requires s == ['a', 'b', 'c', 'd', 'e'] {
        var sSub:seq<char> := s[2..];
        assert false;
      }".TrimStart();
      var documentItem = CreateTestDocument(source, "SequenceDrop.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Equal(2, counterExamples.Length);
      Assert.Contains("sSub is seq<char>", counterExamples[1].Assumption);
      Assert.Matches(new Regex("('a'|s\\[2\\]) == sSub\\[0\\]"), counterExamples[1].Assumption);
      Assert.Matches(new Regex("('b'|s\\[3\\]) == sSub\\[1\\]"), counterExamples[1].Assumption);
      Assert.Matches(new Regex("('c'|s\\[4\\]) == sSub\\[2\\]"), counterExamples[1].Assumption);
      Assert.Contains("|sSub| == 3", counterExamples[1].Assumption);
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
      Assert.Contains("s is seq<char>", counterExamples[0].Assumption);
      Assert.Contains("'a' == s[0]", counterExamples[0].Assumption);
      Assert.Contains("'b' == s[1]", counterExamples[0].Assumption);
      Assert.Contains("'c' == s[2]", counterExamples[0].Assumption);
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
      Assert.Fail("This test needs to be updated");
      // Assert.Equal(1, counterExamples[1].Variables.Count);
      // Assert.True(counterExamples[1].Variables.ContainsKey("m:map<int, bool>"));
      // StringAssert.Matches(counterExamples[1].Variables["m:map<int, bool>"], new Regex("map\\[.*3 := false.*"));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task MapsEmpty(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      method test() {
        var m : map<int,int> := map[];
        assert false;
      }".TrimStart();
      var documentItem = CreateTestDocument(source, "MapsEmpty.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Equal(2, counterExamples.Length);
      Assert.Fail("This test needs to be updated");
      // Assert.Equal(1, counterExamples[1].Variables.Count);
      // Assert.True(counterExamples[1].Variables.ContainsKey("m:map<int, int>"));
      // Assert.Equal("map[]", counterExamples[1].Variables["m:map<int, int>"]);
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
      Assert.Fail("This test needs to be updated");
      // Assert.Single(counterExamples[0].Variables);
      // Assert.True(counterExamples[0].Variables.ContainsKey("c:M.C"));
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
      Assert.Contains("c is (int, bool) ~> real", counterExamples[0].Assumption);
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
      Assert.Fail("This test needs to be updated");
      // Assert.Equal(2, counterExamples[1].Variables.Count);
      // Assert.True(counterExamples[1].Variables.ContainsKey("s:set<map<int, int>>"));
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task DatatypeTypeAsTypeArgument(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      module M {
        datatype C = A | B
        method test(s:set<C>) {
          assert |s| == 0;
        }
      }".TrimStart();
      var documentItem = CreateTestDocument(source, "DatatypeTypeAsTypeArgument.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Single(counterExamples);
      Assert.Contains("exists boundVar0: M.C ::", counterExamples[0].Assumption);
      Assert.Contains("s is set<M.C>", counterExamples[0].Assumption);
      Assert.Contains("boundVar0 in s", counterExamples[0].Assumption);
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
      // the assertion below ensures Dafny does not emit a type constraint if it cannot figure out the variable's type
      Assert.DoesNotContain("?", counterExamples[1].Assumption);
      Assert.Contains("|s| == 0", counterExamples[1].Assumption);
    }

    [Theory]
    [MemberData(nameof(OptionSettings))]
    public async Task MapsUpdate(Action<DafnyOptions> optionSettings) {
      await SetUpOptions(optionSettings);
      var source = @"
      method test(value:int) {
        var m := map[3 := -1];
        m := m[3 := value];
        assert m[3] <= 0;
      }".TrimStart();
      var documentItem = CreateTestDocument(source, "MapsUpdate.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var counterExamples = (await RequestCounterExamples(documentItem.Uri)).
        OrderBy(counterexample => counterexample.Position).ToArray();
      Assert.Equal(3, counterExamples.Length);
      Assert.Contains("m is map<int, int>", counterExamples[0].Assumption);
      Assert.Contains("m is map<int, int>", counterExamples[1].Assumption);
      Assert.Contains("m is map<int, int>", counterExamples[2].Assumption);
      Assert.Contains("m[3] == -1", counterExamples[1].Assumption);
      Assert.Contains("m[3] == value", counterExamples[2].Assumption);
      Assert.Matches(new Regex("value == [1-9][0-9]*"), counterExamples[2].Assumption);
      Assert.DoesNotContain("m[3] == -1", counterExamples[2].Assumption);
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
      Assert.Fail("This test needs to be updated");
      // Assert.Equal(4, counterExamples[2].Variables.Count);
      // Assert.True(counterExamples[2].Variables.ContainsKey("m:map<int, int>"));
      // Assert.True(counterExamples[2].Variables.ContainsKey("m':map<int, int>"));
      // Assert.True(counterExamples[2].Variables.ContainsKey("val:int"));
      // Assert.True(counterExamples[2].Variables.ContainsKey("key:int"));
      // var key = counterExamples[2].Variables["key:int"];
      // var val = counterExamples[2].Variables["val:int"];
      // StringAssert.Matches(counterExamples[2].Variables["m':map<int, int>"], new Regex("map\\[.*" + key + " := " + val + ".*"));
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
      Assert.Fail("This test needs to be updated");
      // Assert.Equal(1, counterExamples[4].Variables.Count);
      // Assert.True(counterExamples[4].Variables.ContainsKey("m:map<int, int>"));
      // StringAssert.Matches(counterExamples[4].Variables["m:map<int, int>"], new Regex("map\\[.*5 := 36.*"));
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
      Assert.Fail("This test needs to be updated");
      // Assert.Equal(4, counterExamples[1].Variables.Count);
      // Assert.True(counterExamples[1].Variables.ContainsKey("m:map<int, int>"));
      // Assert.True(counterExamples[1].Variables.ContainsKey("m':map<int, int>"));
      // Assert.True(counterExamples[1].Variables.ContainsKey("val:int"));
      // Assert.True(counterExamples[1].Variables.ContainsKey("key:int"));
      // var key = counterExamples[1].Variables["key:int"];
      // var val = counterExamples[1].Variables["val:int"];
      // var mapRegex = new Regex("map\\[.*" + key + " := " + val + ".*");
      // Assert.True(mapRegex.IsMatch(counterExamples[1].Variables["m':map<int, int>"]) ||
                    // mapRegex.IsMatch(counterExamples[1].Variables["m:map<int, int>"]));

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
      Assert.Contains("m is map<int, char>", counterExamples[0].Assumption);
      Assert.Contains("25 in m", counterExamples[0].Assumption);
      Assert.Fail("This test needs to be updated");
      // Assert.Equal(2, counterExamples[1].Variables.Count);
      // Assert.True(counterExamples[1].Variables.ContainsKey("m:map<int, char>"));
      // Assert.True(counterExamples[1].Variables.ContainsKey("keys:set<int>"));
      // StringAssert.Matches(counterExamples[1].Variables["m:map<int, char>"], new Regex("map\\[.*25 := .*"));
      // StringAssert.Matches(counterExamples[1].Variables["keys:set<int>"], new Regex("\\{.*25 := true.*"));
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
      Assert.Fail("This test needs to be updated");
      // Assert.Equal(2, counterExamples[1].Variables.Count);
      // Assert.True(counterExamples[1].Variables.ContainsKey("m:map<int, char>"));
      // Assert.True(counterExamples[1].Variables.ContainsKey("values:set<char>"));
      // StringAssert.Matches(counterExamples[1].Variables["m:map<int, char>"], new Regex("map\\[.* := 'c'.*"));
      // StringAssert.Matches(counterExamples[1].Variables["values:set<char>"], new Regex("\\{.*'c' := true.*"));
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
      Assert.Fail("This test needs to be updated");
      // Assert.Equal(1, counterExamples[0].Variables.Count);
      // Assert.True(counterExamples[0].Variables.ContainsKey("m:map<bv2, bv3>"));
      // StringAssert.Matches(counterExamples[0].Variables["m:map<bv2, bv3>"], new Regex("map\\[.*[0-9]+ := [0-9]+.*"));
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
      Assert.Fail("This test needs to be updated");
      // Assert.Equal(1, counterExamples[0].Variables.Count);
      // Assert.True(counterExamples[0].Variables.ContainsKey("this:Mo_dule_.Module2_.Cla__ss"));
      // Assert.Equal("(i := 5)", counterExamples[0].Variables["this:Mo_dule_.Module2_.Cla__ss"]);
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
      Assert.Contains("a is nat64", counterExamples[0].Assumption);
      Assert.Contains("b is nat64", counterExamples[0].Assumption);
      var aRegex = new Regex("assume a == ([0-9]+)");
      var bRegex = new Regex("assume b == ([0-9]+)");
      Assert.Matches(aRegex, counterExamples[0].Assumption);
      Assert.Matches(bRegex, counterExamples[0].Assumption);
      var a = long.Parse(aRegex.Match(counterExamples[0].Assumption).Groups[1].Value);
      var b = long.Parse(bRegex.Match(counterExamples[0].Assumption).Groups[1].Value);
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
      Assert.Fail("This test needs to be updated");
      // Assert.True(counterExamples[0].Variables.ContainsKey("d:M.D"));
      // Assert.Equal("C(i := 123)", counterExamples[0].Variables["d:M.D"]);
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
      Assert.Fail("This test needs to be updated");
      // Assert.True(counterExamples[0].Variables.ContainsKey("s:seq<char>"));
      // Assert.Equal("['a', 'w', 's']", counterExamples[0].Variables["s:seq<char>"]);
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
      Assert.Fail("This test needs to be updated"); // TODO: need to make sure there is a comparison with null
      // Assert.True(counterExamples[0].Variables.ContainsKey("c:M.C?"));
      // Assert.True(counterExamples[0].Variables["c:M.C?"] is
      //  "(c1 := '\\u1023', c2 := '\\u1023')" or
      //  "(c2 := '\\u1023', c1 := '\\u1023')");
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
      Assert.Fail("This test needs to be updated");
      /* First, ensure we can correctly extract counterexamples without crashing... */
      /*var nonIntegralIndexedSeqs = (await RequestCounterExamples(documentItem.Uri))
        .SelectMany(cet => cet.Variables.ToList())
        // Then, extract the number of non-integral indexed sequences from the repro case...
        .Count(IsNegativeIndexedSeq);*/

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
      Assert.Fail("This test needs to be updated");
      // Assert.Equal(3, counterExamples[0].Variables.Count);
      // Assert.True(counterExamples[0].Variables.ContainsKey("a:M.C.Equal$T"));
      // Assert.True(counterExamples[0].Variables.ContainsKey("b:M.C.Equal$T"));
      // Assert.True(counterExamples[0].Variables.ContainsKey("this:M.C<M.C$T>"));
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
