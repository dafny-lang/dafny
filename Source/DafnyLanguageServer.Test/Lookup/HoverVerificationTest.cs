using System;
using System.IO;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using JetBrains.Annotations;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.JsonRpc;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit.Abstractions;
using Xunit;
using XunitAssertMessages;
using Assert = Xunit.Assert;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Lookup {
  [Collection("Sequential Collection")] // Let slow tests run sequentially
  public class HoverVerificationTest : ClientBasedLanguageServerTest {

    private const int MaxTestExecutionTimeMs = 30000;

    [Fact(Timeout = MaxTestExecutionTimeMs)]
    public async Task HoverPutsErrorsFirst() {
      var documentItem = await GetDocumentItem(@"
method {:isolate_assertions} Test(x: int, y: int)
  requires x < y
{
  var callIt := giveIt(x, y);
}
function giveIt(x: int, y: int): int
  requires x != y // OK
  requires 0 < x  // Error
  requires 0 < y  // OK
  requires x + 1 < y // Error
", "HoverPutsErrorsFirst.dfy", true);
      // When hovering the postcondition, it should display the position of the failing path
      await AssertVerificationHoverMatches(documentItem, (3, 21),
        @"**Error:**???**Error:**???**Success:**???**Success:**???"
      );
    }

    [Fact(Timeout = MaxTestExecutionTimeMs)]
    public async Task HoverGetsBasicAssertionInformation() {
      var documentItem = await GetDocumentItem(@"
method Abs(x: int) returns (y: int)
//     ^ Hover #4
    ensures y >= 0
{ //           ^ hover #1
  if x < 2 { // Hover #2 on the brace
    return -x;
  }
  assert x > 2; // Hover #3 on the '>'
  return x;
}
", "testFile.dfy", true);
      // When hovering the postcondition, it should display the position of the failing path
      await AssertVerificationHoverMatches(documentItem, (2, 15),
        @"[**Error:**](???) this postcondition could not be proved on a return path  
This is assertion #??? of 4 in method `Abs`  
Resource usage: ??? RU  
Return path: testFile.dfy(6, 5)"
      );
      // When hovering the failing path, it does not display the position of the failing postcondition
      // because the IDE extension already does it.
      await AssertVerificationHoverMatches(documentItem, (5, 4),
        @"[**Error:**](???) a postcondition could not be proved on this return path???
Could not prove: `y >= 0`  
This is assertion #??? of 4 in method `Abs`  
Resource usage: ??? RU"
      );
      await AssertVerificationHoverMatches(documentItem, (7, 11),
        @"[**Error:**](???) assertion might not hold  
This is assertion #??? of 4 in method `Abs`  
Resource usage: ??? RU"
      );
      await AssertVerificationHoverMatches(documentItem, (0, 7),
        @"**Verification performance metrics for method `Abs`**:

- Total resource usage: ??? RU  
- Only one [assertion batch](???)"
      );
    }

    [Fact(Timeout = MaxTestExecutionTimeMs)]
    public async Task HoverGetsForeignContentAsWell() {
      var documentItem = await GetDocumentItem(@"
include ""foreign-verify.dfy""

predicate Q(i: int) {
  P(i)
}

method DoIt() returns (x: int)
  ensures Q(x)
{
  return -1;
//^ hover #1
}", Path.Combine(Directory.GetCurrentDirectory(), "Lookup/TestFiles/test.dfy"), false);
      // When hovering the failing path, it should extract text from the included file
      await AssertVerificationHoverMatches(documentItem, (9, 4),
        @"[**Error:**](???) a postcondition could not be proved on this return path???
Inside `Q(x)`  
Inside `P(i)`  
Could not prove: `i >= 0`  
This is assertion #1 of 2 in method `DoIt`  
Resource usage: ??? RU"
      );
    }

    [Fact]
    public async Task BetterMessageWhenOneAssertPerBatch() {
      await SetUp(o => {
        o.Set(CommonOptionBag.RelaxDefiniteAssignment, true);
        // LineVerificationStatusOption.Instance.Set(o, true);
      });
      var documentItem = await GetDocumentItem(@"
method {:isolate_assertions} f(x: int) {
  assert x >= 2; // Hover #1
  assert x >= 1; // Hover #2
}
", "testfile.dfy", true);
      await AssertVerificationHoverMatches(documentItem, (1, 12),
        @"[**Error:**](???) assertion might not hold  
This is the only assertion in [batch](???) #??? of ??? in method `f`  
[Batch](???) #??? resource usage: ??? RU"
      );
      await AssertVerificationHoverMatches(documentItem, (2, 12),
        @"<span style='color:green'>**Success:**</span> assertion always holds  
This is the only assertion in [batch](???) #??? of ??? in method `f`  
[Batch](???) #??? resource usage: ??? RU"
      );
      await AssertVerificationHoverMatches(documentItem, (0, 36),
        @"**Verification performance metrics for method `f`**:

- Total resource usage: ??? RU  
- Most costly [assertion batches](https://dafny-lang.github.io/dafny/DafnyRef/DafnyRef#sec-assertion-batches):  
  - #???/??? with 1 assertion at line ???, ??? RU  
  - #???/??? with 1 assertion at line ???, ??? RU"
      );
    }

    [Fact(Timeout = MaxTestExecutionTimeMs)]
    public async Task BetterMessageWhenPreconditionSucceeds() {
      await SetUp(o => {
        o.Set(CommonOptionBag.RelaxDefiniteAssignment, true);
        // LineVerificationStatusOption.Instance.Set(o, true);
      });
      var documentItem = await GetDocumentItem(@"
method Test(i: int)
  requires {:error ""argument should be even"", ""argument is always even""} i % 2 == 0
  requires i > 0
{
}
method main(k: int) {
  Test(2);
  Test(k);
}
", "testfile.dfy", false);
      await AssertVerificationHoverMatches(documentItem, (6, 6),
        @"**Success:**???argument is always even  
Did prove: `i % 2 == 0`"
      );
      await AssertVerificationHoverMatches(documentItem, (6, 6),
        @"**Success:**???the precondition always holds  
Did prove: `i > 0`"
      );
      await AssertVerificationHoverMatches(documentItem, (7, 6),
        @"**Error:**???argument should be even  
Could not prove: `i % 2 == 0`"
      );
      await AssertVerificationHoverMatches(documentItem, (7, 6),
        @"**Error:**???this is the precondition that could not be proved  
Could not prove: `i > 0`"
      );
    }

    [Fact(Timeout = MaxTestExecutionTimeMs)]
    public async Task BetterMessageWhenPostConditionFails() {
      var documentItem = await GetDocumentItem(@"
method Test(j: int) returns (i: int)
  ensures {:error ""return value should be even""} i % 2 == 0
  ensures i > 0
{
  i := j;
}", "testfile.dfy", true);
      await AssertVerificationHoverMatches(documentItem, (3, 0),
        @"**Error:**???return value should be even  
Could not prove: `i % 2 == 0`"
      );

      await AssertVerificationHoverMatches(documentItem, (3, 0),
        @"**Error:**???a postcondition could not be proved on this return path  
Could not prove: `i > 0`"
      );
    }

    [Fact(Timeout = MaxTestExecutionTimeMs)]
    public async Task MessagesWhenMultipleAssertionsPerBatch() {
      var documentItem = await GetDocumentItem(@"
function f(x: int): int {
  assert x >= 4;
  assert x >= 2; // Hover #1
  assert {:split_here} x >= 5; // hover #2
  assert x >= 1;
  x
}
", "testfile.dfy", false);
      await AssertVerificationHoverMatches(documentItem, (2, 12),
        @"???Success??? assertion always holds  
This is assertion #2 of 2 in [batch](???) #1 of 2 in function `f`  
[Batch](???) #1 resource usage: ??? RU"
      );
      await AssertVerificationHoverMatches(documentItem, (3, 26),
        @"[**Error:**](???) assertion might not hold  
This is assertion #1 of 2 in [batch](???) #2 of 2 in function `f`  
[Batch](???) #2 resource usage: ??? RU"
      );
      await AssertVerificationHoverMatches(documentItem, (0, 36),
        @"**Verification performance metrics for function `f`**:

- Total resource usage: ??? RU  
- Most costly [assertion batches](https://dafny-lang.github.io/dafny/DafnyRef/DafnyRef#sec-assertion-batches):  
  - #???/2 with 2 assertions at line ???, ??? RU  
  - #???/2 with 2 assertions at line ???, ??? RU"
      );
    }

    [Fact]
    public async Task MeaningfulMessageWhenMethodWithoutAssert() {
      var documentItem = await GetDocumentItem(@"
method f(x: int) {
  print x;
}", "testfile.dfy", true);
      await AssertVerificationHoverMatches(documentItem, (0, 7),
        @"**Verification performance metrics for method `f`**:

No assertions."
      );
      await AssertVerificationHoverMatches(documentItem, (0, 9),
        "```dafny\nx: int\n```");
    }


    [Fact(Timeout = MaxTestExecutionTimeMs)]
    public async Task MeaningfulMessageForFailingPreconditions() {
      var documentItem = await GetDocumentItem(@"
method Test1() {
    Test2(0);  // Hover #1
}

method Test2(i: int)
  requires i > 0 {

}", "testfile.dfy", false);
      await AssertVerificationHoverMatches(documentItem, (1, 10),
        @"???
Failing precondition:???"
      );
    }

    [Fact(Timeout = MaxTestExecutionTimeMs)]
    public async Task MeaningfulMessageWhenMethodWithOneAssert() {
      var documentItem = await GetDocumentItem(@"
method f(x: int) {
  assert false;
}", "testfile1.dfy", true);
      await AssertVerificationHoverMatches(documentItem, (0, 7),
        @"**Verification performance metrics for method `f`**:

- Total resource usage: ??? RU  
- Only one [assertion batch](???) containing 1 assertion."
      );
    }


    [Fact(Timeout = MaxTestExecutionTimeMs)]
    public async Task MeaningfulMessageWhenMethodWithTwoAsserts() {
      var documentItem = await GetDocumentItem(@"
method f(x: int) {
  assert false;
  assert false;
}", "testfile2.dfy", false);
      await AssertVerificationHoverMatches(documentItem, (0, 7),
        @"**Verification performance metrics for method `f`**:

- Total resource usage: ??? RU  
- Only one [assertion batch](???) containing 2 assertions."
      );
    }

    [Fact(Timeout = MaxTestExecutionTimeMs)]
    public async Task DoNotExtendPastExpressions2() {
      var documentItem = await GetDocumentItem(@"
function Id<T>(t: T): T { t }
datatype Test = Test(i: int)
{
  method Tester(other: Test) {
    assert Valid(other);
    assert CanAct(Id(other));
  }
  static predicate Valid(t: Test) {
    t.i > 0
  }
  static predicate CanAct(t: Test) requires Valid(t) {
    t.i > 1
  }
}
", "testfile2.dfy", true);
      await AssertVerificationHoverMatches(documentItem, (4, 20),
        @"**Error:**???assertion might not hold???
Could not prove: `t.i > 0`  "
      );
      await AssertVerificationHoverMatches(documentItem, (5, 20),
        @"**Error:**???assertion might not hold???
Could not prove: `t.i > 1`  "
      );
      await AssertVerificationHoverMatches(documentItem, (5, 20),
        @"**Success:**???function precondition satisfied???
Inside `Valid(t)`  
Did prove: `t.i > 0`  "
      );
    }

    [Fact/*(Timeout = MaxTestExecutionTimeMs)*/]
    public async Task DoNotExtendPastExpressions3() {
      var documentItem = await GetDocumentItem(@"
datatype ValidTester = Tester(next: ValidTester2) | Tester2(next: ValidTester2) | Test3(next: ValidTester2)
{
  predicate Valid() {
    ((this.Tester? || this.Tester2?) && this.next.Valid()) || (this.Test3? && !this.next.Valid())
  }

  function apply(): int requires Valid() {
    2
  }
  static method Test(c: ValidTester) {
    var x := c.apply();
  }
}

datatype ValidTester2 = MoreTest(i: int, next: ValidTester2) | End {
  predicate Valid(defaultValue: int := 0) {
    0 <= defaultValue && (this.End? || (this.MoreTest? && this.next.Valid() && i > 0))
  }
}
", "testfile2.dfy", false);
      await AssertVerificationHoverMatches(documentItem, (10, 16),
        @"**Error:**???function precondition could not be proved???
Inside `Valid()`  
Could not prove: `((this.Tester? || this.Tester2?) && this.next.Valid()) || (this.Test3? && !this.next.Valid())`  "
      );
    }

    [Fact]
    public async Task DoNotExtendPastExpressions() {
      var documentItem = await GetDocumentItem(@"
datatype Test = Test(i: int)
{
  predicate Valid() {
    i > 0
  }
  predicate CanAct() requires Valid() {
    i > 1
  }
  method Tester(other: Test) {
    assert other.Valid();
    assert Id(other).CanAct();
  }
}
function Id<T>(t: T): T { t }

", "testfile2.dfy", true);
      await AssertVerificationHoverMatches(documentItem, (9, 20),
        @"**Error:**???assertion might not hold???
Could not prove: `i > 0`  "
      );
      await AssertVerificationHoverMatches(documentItem, (10, 20),
      @"**Error:**???assertion might not hold???
Could not prove: `i > 1`  "
    );
      await AssertVerificationHoverMatches(documentItem, (10, 20),
        @"**Success:**???function precondition satisfied???
Inside `Valid()`  
Did prove: `i > 0`  "
      );
    }

    [Fact()]
    public async Task DisplayNestedFailingPostconditionsAndPreconditions() {
      var documentItem = await GetDocumentItem(@"
predicate P(i: int) {
  i <= 0
}

predicate Q(i: int, j: int) {
  i == j || -i == j
}

function Toast(i: int): int
  requires P(i)

method Test(i: int) returns (j: nat)
  ensures Q(i, j)
{
  if i < 0 {
    return -i;
  } else {
    return Toast(i);
  }
}
", "testfile2.dfy", false);
      await AssertVerificationHoverMatches(documentItem, (12, 11),
        @"**Error:**???this postcondition could not be proved on a return path???
Could not prove: `i == j || -i == j`???
Return path: testfile2.dfy(18, 5)"
      );
      await AssertVerificationHoverMatches(documentItem, (17, 6),
        @"**Error:**???a postcondition could not be proved on this return path???
Inside `Q(i, j)`???
Could not prove: `i == j || -i == j`"
      );
      await AssertVerificationHoverMatches(documentItem, (17, 13),
        @"**Error:**???function precondition could not be proved???
Inside `P(i)`???
Could not prove: `i <= 0`"
      );
    }

    [Fact/*(Timeout = MaxTestExecutionTimeMs)*/]
    public async Task DisplayWorksOnPreviouslyFailingExample() {
      var documentItem = await GetDocumentItem(@"
module ProblemModule {
  datatype X =
    | Cons(head: int, tail: X)
    | Nil
  {
    predicate Valid() {
      this.Cons? && tail.Valid()
    }
  }
}

method Test() returns (j: int)
  ensures j == 1
{
  return 2;
}
", "testfile2.dfy", true);
      await AssertVerificationHoverMatches(documentItem, (14, 5),
        @"**Error:**???a postcondition could not be proved on this return path???
Could not prove: `j == 1`"
      );
    }

    [Fact(Timeout = MaxTestExecutionTimeMs)]
    public async Task DoNotDisplayVerificationIfSyntaxError() {
      var documentItem = await GetDocumentItem(@"
predicate P(i: int) {
  i <= 0
}

method Test(i: int)
{
  assert P(1);
}
", "testfile2.dfy", false);
      await AssertVerificationHoverMatches(documentItem, (6, 11),
        @"**Error:**???assertion might not hold  
Inside `P(1)`  
Could not prove: `i <= 0`"
      );
      await ApplyChangesAndWaitCompletionAsync(
        ref documentItem,
        new TextDocumentContentChangeEvent {
          Range = ((0, 0), (0, 0)),
          Text = @"/"
        });
      await AssertVerificationHoverMatches(documentItem, (6, 11),
        "No hover information available due to program error"
      );
    }
    [Fact(Timeout = 5 * MaxTestExecutionTimeMs)]
    public async Task IndicateClickableWarningSignsOnMethodHoverWhenResourceLimitReached10MThreshold() {
      var documentItem = await GetDocumentItem(@"
ghost function f(i:nat, j:nat):int {if i == 0 then 0 else f(i - 1, i * j + 1) + f(i - 1, 2 * i * j)}

lemma{:resource_limit 10000000} L()
{
  assert f(10, 5) == 0;
} ", "testfileSlow.dfy", true);
      await AssertVerificationHoverMatches(documentItem, (2, 22),
        @"**Verification performance metrics for method `L`**:

- Total resource usage: ??? RU [⚠](???)"
      );
    }


    public HoverVerificationTest(ITestOutputHelper output) : base(output) {
    }
  }
}
