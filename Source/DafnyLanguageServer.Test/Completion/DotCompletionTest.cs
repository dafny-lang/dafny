using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Completion {
  [TestClass]
  public class DotCompletionTest : DafnyLanguageServerTestBase {
    // At this time, the main logic happens within ISymbolGuesser since we have to primarily work
    // with migrated symbol tables. Therefore, we apply modifications prior requesting completion
    // just like a user would do.
    private ILanguageClient client;

    private void ApplyChanges(TextDocumentItem documentItem, params TextDocumentContentChangeEvent[] changes) {
      client.DidChangeTextDocument(new DidChangeTextDocumentParams {
        TextDocument = new OptionalVersionedTextDocumentIdentifier {
          Uri = documentItem.Uri,
          Version = documentItem.Version + 1
        },
        ContentChanges = changes
      });
    }

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

    [TestInitialize]
    public async Task SetUp() {
      client = await InitializeClient();
    }

    [TestMethod]
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
      ApplyChanges(
        documentItem,
        new TextDocumentContentChangeEvent {
          Range = new Range((4, 10), (4, 10)),
          Text = " + this."
        }
      );

      var completionList = await RequestCompletionAsync(documentItem, (4, 18));
      Assert.AreEqual(2, completionList.Count);
      Assert.AreEqual(CompletionItemKind.Function, completionList[0].Kind);
      Assert.AreEqual("GetX", completionList[0].Label);
      Assert.AreEqual(CompletionItemKind.Field, completionList[1].Kind);
      Assert.AreEqual("x", completionList[1].Label);
    }

    [TestMethod]
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
      ApplyChanges(
        documentItem,
        new TextDocumentContentChangeEvent {
          Range = new Range((4, 4), (4, 10)),
          Text = "."
        }
      );

      var completionList = await RequestCompletionAsync(documentItem, (4, 5));
      Assert.AreEqual(0, completionList.Count);
    }

    [TestMethod]
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
      ApplyChanges(
        documentItem,
        new TextDocumentContentChangeEvent {
          Range = new Range((4, 0), (4, 10)),
          Text = "."
        }
      );

      var completionList = await RequestCompletionAsync(documentItem, (4, 1));
      Assert.AreEqual(0, completionList.Count);
    }

    [TestMethod]
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
      ApplyChanges(
        documentItem,
        new TextDocumentContentChangeEvent {
          Range = new Range((4, 10), (4, 10)),
          Text = "."
        }
      );

      var completionList = await RequestCompletionAsync(documentItem, (4, 11));
      Assert.AreEqual(0, completionList.Count);
    }

    [TestMethod]
    public async Task CompleteOnLocalArrayReturnsLength() {
      var source = @"
method DoIt() {
  var x := new int[10];
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      ApplyChanges(
        documentItem,
        new TextDocumentContentChangeEvent {
          Range = new Range((1, 23), (1, 23)),
          Text = @"
  var y := x."
        }
      );

      var completionList = await RequestCompletionAsync(documentItem, (2, 13));
      Assert.AreEqual(1, completionList.Count);
      Assert.AreEqual(CompletionItemKind.Field, completionList[0].Kind);
      Assert.AreEqual("Length", completionList[0].Label);
    }

    [TestMethod]
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
      ApplyChanges(
        documentItem,
        new TextDocumentContentChangeEvent {
          Range = new Range((4, 21), (4, 21)),
          Text = @"
    var y := x."
        }
      );

      var completionList = await RequestCompletionAsync(documentItem, (5, 15));
      Assert.AreEqual(1, completionList.Count);
      Assert.AreEqual(CompletionItemKind.Field, completionList[0].Kind);
      Assert.AreEqual("b", completionList[0].Label);
    }

    [TestMethod]
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
      ApplyChanges(
        documentItem,
        new TextDocumentContentChangeEvent {
          Range = new Range((4, 21), (4, 21)),
          Text = @"
    var y := this.x."
        }
      );

      var completionList = await RequestCompletionAsync(documentItem, (5, 20));
      Assert.AreEqual(1, completionList.Count);
      Assert.AreEqual(CompletionItemKind.Field, completionList[0].Kind);
      Assert.AreEqual("Length", completionList[0].Label);
    }

    [TestMethod]
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
      ApplyChanges(
        documentItem,
        new TextDocumentContentChangeEvent {
          Range = new Range((8, 0), (8, 0)),
          Text = "    var l := b.c.x."
        }
      );

      var completionList = await RequestCompletionAsync(documentItem, (8, 19));
      Assert.AreEqual(1, completionList.Count);
      Assert.AreEqual(CompletionItemKind.Method, completionList[0].Kind);
      Assert.AreEqual("GetConstant", completionList[0].Label);
    }
  }
}
