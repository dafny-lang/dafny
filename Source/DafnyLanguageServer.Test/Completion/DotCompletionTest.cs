using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Xunit;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Completion {
  public class DotCompletionTest : ClientBasedLanguageServerTest {

    private async Task<List<CompletionItem>> RequestCompletionAsync(TextDocumentItem documentItem, Position position) {
      // TODO at this time we do not set the context since it appears that's also the case when used within VSCode.
      var completionList = await client.RequestCompletion(
        new CompletionParams {
          TextDocument = documentItem.Uri,
          Position = position
        },
        CancellationToken
      ).AsTask();
      return completionList.OrderBy(completion => completion.Label).ToList();
    }

    [Fact]
    public async Task CompleteOnThisReturnsClassMembers() {
      var source = @"
class A {
  var x: int;

  function GetX(): int {
    this.x
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      ApplyChange(ref documentItem, new Range(4, 10, 4, 10), " + this.");

      var completionList = await RequestCompletionAsync(documentItem, (4, 18));
      Assert.Equal(2, completionList.Count);
      Assert.Equal(CompletionItemKind.Function, completionList[0].Kind);
      Assert.Equal("GetX", completionList[0].Label);
      Assert.Equal(CompletionItemKind.Field, completionList[1].Kind);
      Assert.Equal("x", completionList[1].Label);
    }

    [Fact]
    public async Task CompleteOnNothingReturnsEmptyList() {
      var source = @"
class A {
  var x: int;

  function GetX(): int {
    this.x
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      ApplyChange(ref documentItem, new Range((4, 4), (4, 10)), ".");

      var completionList = await RequestCompletionAsync(documentItem, (4, 5));
      Assert.Empty(completionList);
    }

    [Fact]
    public async Task CompleteOnNothingAtLineStartReturnsEmptyList() {
      var source = @"
class A {
  var x: int;

  function GetX(): int {
    this.x
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      ApplyChange(ref documentItem, new Range((4, 0), (4, 10)), ".");

      var completionList = await RequestCompletionAsync(documentItem, (4, 1));
      Assert.Empty(completionList);
    }

    [Fact]
    public async Task CompleteOnTypeWithoutMembersReturnsEmptyList() {
      var source = @"
class A {
  var x: int;

  function GetX(): int {
    this.x
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      ApplyChange(ref documentItem, new Range((4, 10), (4, 10)), ".");

      var completionList = await RequestCompletionAsync(documentItem, (4, 11));
      Assert.Empty(completionList);
    }

    [Fact]
    public async Task CompleteOnLocalArrayReturnsLength() {
      var source = @"
method DoIt() {
  var x := new int[10];
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      ApplyChange(ref documentItem, new Range((1, 23), (1, 23)), @"
  var y := x.");

      var completionList = await RequestCompletionAsync(documentItem, (2, 13));
      Assert.Single(completionList);
      Assert.Equal(CompletionItemKind.Field, completionList[0].Kind);
      Assert.Equal("Length", completionList[0].Label);
    }

    [Fact]
    public async Task CompleteOnShadowedVariableReturnsCompletionOfClosestSymbol() {
      var source = @"
class A {
  var x: array<int>;

  method DoIt() {
    var x := new B();
  }
}

class B {
  var b: int;

  constructor() { }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      ApplyChange(ref documentItem, new Range((4, 21), (4, 21)), @"
    var y := x.");

      var completionList = await RequestCompletionAsync(documentItem, (5, 15));
      Assert.Single(completionList);
      Assert.Equal(CompletionItemKind.Field, completionList[0].Kind);
      Assert.Equal("b", completionList[0].Label);
    }

    [Fact]
    public async Task CompleteOnShadowedVariableReturnsCompletionOfClassIfPrefixedWithThis() {
      var source = @"
class A {
  var x: array<int>;

  method DoIt() {
    var x := new B();
  }
}

class B {
  var b: int;

  constructor() { }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      ApplyChange(ref documentItem, new Range((4, 21), (4, 21)), @"
    var y := this.x.");

      var completionList = await RequestCompletionAsync(documentItem, (5, 20));
      Assert.Single(completionList);
      Assert.Equal(CompletionItemKind.Field, completionList[0].Kind);
      Assert.Equal("Length", completionList[0].Label);
    }

    [Fact]
    public async Task CompleteOnMemberAccessChainRespectsCompleteChain() {
      var source = @"
class A {
  var b: B;

  constructor() {
    b := new B();
  }

  method DoIt() {

  }
}

class B {
  var c: C;

  constructor() {
    c := new C();
  }
}

class C {
  var x: X;

  constructor() {
    x := new X();
  }
}

class X {
  method GetConstant() returns (c: int) {
    return 1;
  }

  constructor() { }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

      ApplyChange(ref documentItem, new Range((8, 0), (8, 0)), "    var l := b.c.x.");

      var completionList = await RequestCompletionAsync(documentItem, (8, 19));
      Assert.Single(completionList);
      Assert.Equal(CompletionItemKind.Method, completionList[0].Kind);
      Assert.Equal("GetConstant", completionList[0].Label);
    }
  }
}
