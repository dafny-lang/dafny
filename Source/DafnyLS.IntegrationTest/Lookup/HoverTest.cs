using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.IO;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Lookup {
  [TestClass]
  public class HoverTest : DafnyLanguageServerTestBase {
    private ILanguageClient _client;

    [TestInitialize]
    public async Task SetUp() {
      _client = await InitializeClient();
    }

    private Task<Hover> RequestHover(TextDocumentItem documentItem, Position position) {
      return _client.RequestHover(
        new HoverParams {
          TextDocument = documentItem.Uri,
          Position = position
        },
        CancellationToken
      );
    }

    [TestMethod]
    public async Task HoveringMethodInvocationOfMethodDeclaredInSameDocumentReturnsSignature() {
      var source = @"
method DoIt() returns (x: int) {
}

method CallDoIt() returns () {
  var x := DoIt();
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var hover = await RequestHover(documentItem, (4, 14));
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nmethod DoIt() returns (x: int)\n```", markup.Value);
    }

    [TestMethod]
    public async Task HoveringFieldOfSystemTypeReturnsDefinition() {
      var source = @"
method DoIt() {
  var x := new int[0];
  var y := x.Length;
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var hover = await RequestHover(documentItem, (2, 14));
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nconst array.Length: int\n```", markup.Value);
    }

    [TestMethod]
    public async Task HoveringFunctionInvocationOfFunctionDeclaredInForeignDocumentReturnsSignature() {
      // TODO Actually, the invoked function is a function method.
      var source = @"
include ""foreign.dfy""

method DoIt() returns (x: int) {
  var a := new A();
  return a.GetX();
}".TrimStart();
      var documentItem = CreateTestDocument(source, Path.Combine(Directory.GetCurrentDirectory(), "Lookup/TestFiles/test.dfy"));
      _client.OpenDocument(documentItem);
      var hover = await RequestHover(documentItem, (4, 13));
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nfunction A.GetX(): int\n```", markup.Value);
    }

    [TestMethod]
    public async Task HoveringInvocationOfUnknownFunctionOrMethodReturnsEmptyHover() {
      var source = @"
method DoIt() returns (x: int) {
  return GetX();
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var hover = await RequestHover(documentItem, (1, 12));
      Assert.IsNotNull(hover);
      Assert.IsNull(hover.Contents.MarkupContent);
    }

    [TestMethod]
    public async Task HoveringVariableShadowingFieldReturnsTheVariable() {
      var source = @"
class Test {
  var x: int;

  method DoIt() {
    var x := """";
    print x;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var hover = await RequestHover(documentItem, (5, 10));
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nx: string\n```", markup.Value);
    }

    [TestMethod]
    public async Task HoveringVariableShadowingFieldReturnsTheFieldIfThisIsUsed() {
      var source = @"
class Test {
  var x: int;

  method DoIt() {
    var x := 1;
    print this.x;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var hover = await RequestHover(documentItem, (5, 15));
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nvar Test.x: int\n```", markup.Value);
    }

    [TestMethod]
    public async Task HoveringVariableShadowingAnotherVariableReturnsTheShadowingVariable() {
      var source = @"
class Test {
  var x: int;

  method DoIt() {
    var x := 1;
    {
      var x := ""2"";
      print x;
    }
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var hover = await RequestHover(documentItem, (7, 12));
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nx: string\n```", markup.Value);
    }

    [TestMethod]
    public async Task HoveringVariableShadowedByAnotherReturnsTheOriginalVariable() {
      var source = @"
class Test {
  var x: int;

  method DoIt() {
    var x := ""1"";
    {
      var x := 2;
    }
    print x;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var hover = await RequestHover(documentItem, (8, 10));
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nx: string\n```", markup.Value);
    }

    [TestMethod]
    public async Task HoveringTypeOfFieldReturnsTheUserDefinedType() {
      var source = @"
class A {
  constructor() {}
}

class B {
  var a: A;

  constructor() {
    a := new A();
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var hover = await RequestHover(documentItem, (5, 9));
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nclass A\n```", markup.Value);
    }

    [TestMethod]
    public async Task HoveringTypeOfConstructorInvocationReturnsTheUserDefinedType() {
      var source = @"
class A {
  constructor() {}
}

class B {
  var a: A;

  constructor() {
    a := new A();
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var hover = await RequestHover(documentItem, (8, 13));
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nclass A\n```", markup.Value);
    }

    [TestMethod]
    public async Task HoveringParameterOfMethodReturnsTheUserDefinedType() {
      var source = @"
class A {
  constructor() {}
}

method DoIt(a: A) {}".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var hover = await RequestHover(documentItem, (4, 15));
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nclass A\n```", markup.Value);
    }
  }
}
