using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Progress;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reactive.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Workspace;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Lookup {
  [TestClass]
  public class DefinitionTest : DafnyLanguageServerTestBase {
    private ILanguageClient client;
    private DiagnosticsReceiver diagnosticReceiver;

    [TestInitialize]
    public async Task SetUp() {
      diagnosticReceiver = new();
      client = await InitializeClient();
    }

    private IRequestProgressObservable<IEnumerable<LocationOrLocationLink>, LocationOrLocationLinks> RequestDefinition(TextDocumentItem documentItem, Position position) {
      return client.RequestDefinition(
        new DefinitionParams {
          TextDocument = documentItem.Uri,
          Position = position
        },
        CancellationToken
      );
    }

    [TestMethod]
    public async Task DefinitionOfMethodInvocationOfMethodDeclaredInSameDocumentReturnsLocation() {
      var source = @"
method DoIt() returns (x: int) {
}

method CallDoIt() returns () {
  var x := DoIt();
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var definition = (await RequestDefinition(documentItem, (4, 14)).AsTask()).Single();
      var location = definition.Location;
      Assert.AreEqual(documentItem.Uri, location.Uri);
      Assert.AreEqual(new Range((0, 7), (0, 11)), location.Range);
    }

    [TestMethod]
    public async Task DefinitionReturnsBeforeVerificationIsComplete() {
      var documentItem = CreateTestDocument(NeverVerifies);
      client.OpenDocument(documentItem);
      var verificationTask = diagnosticReceiver.AwaitVerificationDiagnosticsAsync(CancellationToken);
      var definitionTask = RequestDefinition(documentItem, (4, 14)).AsTask();
      var first = await Task.WhenAny(verificationTask, definitionTask);
      Assert.AreSame(first, definitionTask);
    }

    [TestMethod]
    public async Task DefinitionOfFieldOfSystemTypeReturnsNoLocation() {
      var source = @"
method DoIt() {
  var x := new int[0];
  var y := x.Length;
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      Assert.IsFalse((await RequestDefinition(documentItem, (2, 14)).AsTask()).Any());
    }

    [TestMethod]
    public async Task DefinitionOfFunctionInvocationOfFunctionDeclaredInForeignDocumentReturnsLocation() {
      var source = @"
include ""foreign.dfy""

method DoIt() returns (x: int) {
  var a := new A();
  return a.GetX();
}".TrimStart();
      var documentItem = CreateTestDocument(source, Path.Combine(Directory.GetCurrentDirectory(), "Lookup/TestFiles/test.dfy"));
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var definition = (await RequestDefinition(documentItem, (4, 13)).AsTask()).Single();
      var location = definition.Location;
      Assert.AreEqual(DocumentUri.FromFileSystemPath(Path.Combine(Directory.GetCurrentDirectory(), "Lookup/TestFiles/foreign.dfy")), location.Uri);
      Assert.AreEqual(new Range((5, 18), (5, 22)), location.Range);
    }

    [TestMethod]
    public async Task DefinitionOfInvocationOfUnknownFunctionOrMethodReturnsNoLocation() {
      var source = @"
method DoIt() returns (x: int) {
  return GetX();
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      Assert.IsFalse((await RequestDefinition(documentItem, (1, 12)).AsTask()).Any());
    }

    [TestMethod]
    public async Task DefinitionOfVariableShadowingFieldReturnsTheVariable() {
      var source = @"
class Test {
  var x: int;

  method DoIt() {
    var x := 1;
    print x;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var definition = (await RequestDefinition(documentItem, (5, 10)).AsTask()).Single();
      var location = definition.Location;
      Assert.AreEqual(documentItem.Uri, location.Uri);
      Assert.AreEqual(new Range((4, 8), (4, 9)), location.Range);
    }

    [TestMethod]
    public async Task DefinitionOfVariableShadowingFieldReturnsTheFieldIfThisIsUsed() {
      var source = @"
class Test {
  var x: int;

  method DoIt() {
    var x := 1;
    print this.x;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var definition = (await RequestDefinition(documentItem, (5, 15)).AsTask()).Single();
      var location = definition.Location;
      Assert.AreEqual(documentItem.Uri, location.Uri);
      Assert.AreEqual(new Range((1, 6), (1, 7)), location.Range);
    }

    [TestMethod]
    public async Task DefinitionOfVariableShadowingAnotherVariableReturnsTheShadowingVariable() {
      var source = @"
class Test {
  var x: int;

  method DoIt() {
    var x := 1;
    {
      var x := 2;
      print x;
    }
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var definition = (await RequestDefinition(documentItem, (7, 12)).AsTask()).Single();
      var location = definition.Location;
      Assert.AreEqual(documentItem.Uri, location.Uri);
      Assert.AreEqual(new Range((6, 10), (6, 11)), location.Range);
    }

    [TestMethod]
    public async Task DefinitionOfVariableShadowedByAnotherReturnsTheOriginalVariable() {
      var source = @"
class Test {
  var x: int;

  method DoIt() {
    var x := 1;
    {
      var x := 2;
    }
    print x;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var definition = (await RequestDefinition(documentItem, (8, 10)).AsTask()).Single();
      var location = definition.Location;
      Assert.AreEqual(documentItem.Uri, location.Uri);
      Assert.AreEqual(new Range((4, 8), (4, 9)), location.Range);
    }

    [TestMethod]
    public async Task DefinitionInConstructorInvocationOfUserDefinedTypeOfForeignFileReturnsLinkToForeignFile() {
      var source = @"
include ""foreign.dfy""

method DoIt() returns (x: int) {
  var a := new A();
  return a.GetX();
}".TrimStart();
      var documentItem = CreateTestDocument(source, Path.Combine(Directory.GetCurrentDirectory(), "Lookup/TestFiles/test.dfy"));
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var definition = (await RequestDefinition(documentItem, (3, 15)).AsTask()).Single();
      var location = definition.Location;
      Assert.AreEqual(DocumentUri.FromFileSystemPath(Path.Combine(Directory.GetCurrentDirectory(), "Lookup/TestFiles/foreign.dfy")), location.Uri);
      Assert.AreEqual(new Range((0, 6), (0, 7)), location.Range);
    }
  }
}
