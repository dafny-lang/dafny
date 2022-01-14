using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Linq;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Lookup {
  [TestClass]
  public class SignatureHelpTest : DafnyLanguageServerTestBase {
    // At this time, the main logic happens within ISymbolGuesser since we have to primarily work
    // with migrated symbol tables. Therefore, we apply modifications prior requesting signature help
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

    private Task<SignatureHelp> RequestSignatureHelpAsync(TextDocumentItem documentItem, Position position) {
      // TODO at this time we do not set the context since it appears that's also the case when used within VSCode.
      return client.RequestSignatureHelp(
        new SignatureHelpParams {
          TextDocument = documentItem.Uri,
          Position = position
        },
        CancellationToken
      );
    }

    [TestInitialize]
    public async Task SetUp() {
      client = await InitializeClient();
    }

    [TestMethod]
    public async Task SignatureHelpForUnloadedDocumentReturnsNull() {
      var documentItem = CreateTestDocument("");
      var signatureHelp = await RequestSignatureHelpAsync(documentItem, (7, 11));
      Assert.IsNull(signatureHelp);
    }

    [TestMethod]
    public async Task SignatureHelpOnOpeningParenthesesReturnsSignatureForExistingMethod() {
      var source = @"
method Multiply(x: int, y: int) returns (p: int)
  ensures p == x * y
{
  return x * y;
}

method Main() {
  //
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      ApplyChanges(
        documentItem,
        new TextDocumentContentChangeEvent {
          Range = new Range((7, 2), (7, 2)),
          Text = "Multiply("
        }
      );

      var signatureHelp = await RequestSignatureHelpAsync(documentItem, (7, 11));
      var signatures = signatureHelp.Signatures.ToArray();
      Assert.AreEqual(1, signatures.Length);
      var markup = signatures[0].Documentation.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nmethod Multiply(x: int, y: int) returns (p: int)\n```", markup.Value);
    }

    [TestMethod]
    public async Task SignatureHelpOnOpeningParenthesesReturnsSignatureForExistingFunction() {
      var source = @"
function Multiply(x: int, y: int): int
{
  x * y
}

method Main() {
  //
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      ApplyChanges(
        documentItem,
        new TextDocumentContentChangeEvent {
          Range = new Range((6, 2), (6, 2)),
          Text = "Multiply("
        }
      );

      var signatureHelp = await RequestSignatureHelpAsync(documentItem, (6, 11));
      var signatures = signatureHelp.Signatures.ToArray();
      Assert.AreEqual(1, signatures.Length);
      var markup = signatures[0].Documentation.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nfunction Multiply(x: int, y: int): int\n```", markup.Value);
    }

    [TestMethod]
    public async Task SignatureHelpOnOpeningParenthesesReturnsNullIfNoSuchMethodOrFunctionExists() {
      var source = @"
method Main() {
  //
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      ApplyChanges(
        documentItem,
        new TextDocumentContentChangeEvent {
          Range = new Range((1, 2), (1, 2)),
          Text = "Multiply("
        }
      );

      var signatureHelp = await RequestSignatureHelpAsync(documentItem, (1, 11));
      Assert.IsNull(signatureHelp);
    }

    [TestMethod]
    public async Task SignatureHelpOnOpeningParenthesesReturnsSignatureOfClosestFunction() {
      var source = @"
function Multiply(x: int, y: int): int
{
  x * y
}

module Mod {
  function Multiply(a: int, b: int): int
  {
    a * b
  }

  class SomeClass {
    function Multiply(n: int, m: int): int
    {
      n * m
    }

    method GetProduct(x: int, y: int) returns (p: int)
      ensures p == x * y
    {
      //
    }
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      ApplyChanges(
        documentItem,
        new TextDocumentContentChangeEvent {
          Range = new Range((20, 6), (20, 6)),
          Text = "Multiply("
        }
      );

      var signatureHelp = await RequestSignatureHelpAsync(documentItem, (20, 15));
      var signatures = signatureHelp.Signatures.ToArray();
      Assert.AreEqual(1, signatures.Length);
      var markup = signatures[0].Documentation.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nfunction SomeClass.Multiply(n: int, m: int): int\n```", markup.Value);
    }

    [TestMethod]
    public async Task SignatureHelpOnOpeningParenthesesReturnsSignatureOfClassMemberOfDesignator() {
      var source = @"
class A {
  constructor() {}

  function Multiply(n: int, m: int): int
  {
    n * m
  }
}


class B {
  var a: A;

  constructor() {
    a := new A();
  }

  function Multiply(x: int, y: int): int
  {
    x * y
  }

  method GetProduct(x: int, y: int) returns (p: int)
    ensures p == x * y
  {
    //
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      ApplyChanges(
        documentItem,
        new TextDocumentContentChangeEvent {
          Range = new Range((25, 4), (25, 4)),
          Text = "a.Multiply("
        }
      );

      var signatureHelp = await RequestSignatureHelpAsync(documentItem, (25, 15));
      var signatures = signatureHelp.Signatures.ToArray();
      Assert.AreEqual(1, signatures.Length);
      var markup = signatures[0].Documentation.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nfunction A.Multiply(n: int, m: int): int\n```", markup.Value);
    }
  }
}
