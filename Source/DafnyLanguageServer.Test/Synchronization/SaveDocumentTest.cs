using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Configuration;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using System.Collections.Generic;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization {
  [TestClass]
  public class SaveDocumentTest : DafnyLanguageServerTestBase {
    private ILanguageClient client;
    private IDictionary<string, string> configuration;

    [TestInitialize]
    public Task SetUp() => SetUp(null);

    public async Task SetUp(IDictionary<string, string> configuration) {
      this.configuration = configuration;
      client = await InitializeClient();
    }

    protected override IConfiguration CreateConfiguration() {
      return configuration == null
        ? base.CreateConfiguration()
        : new ConfigurationBuilder().AddInMemoryCollection(configuration).Build();
    }

    [TestMethod]
    public async Task LeavesDocumentUnchangedIfVerifyOnChange() {
      var source = @"
function GetConstant(): int {
  1
}".Trim();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var openedDocument = await Documents.GetDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(openedDocument);
      await client.SaveDocumentAndWaitAsync(documentItem, CancellationToken);
      var savedDocument = await Documents.GetDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(savedDocument);
      Assert.AreSame(openedDocument, savedDocument);
    }

    [TestMethod]
    public async Task LeavesDocumentUnchangedIfVerifyNever() {
      var source = @"
function GetConstant(): int {
  1
}".Trim();
      await SetUp(new Dictionary<string, string>() {
        { $"{DocumentOptions.Section}:{nameof(DocumentOptions.Verify)}", nameof(AutoVerification.Never) }
      });
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var openedDocument = await Documents.GetDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(openedDocument);
      await client.SaveDocumentAndWaitAsync(documentItem, CancellationToken);
      var savedDocument = await Documents.GetDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(savedDocument);
      Assert.AreSame(openedDocument, savedDocument);
    }

    [TestMethod]
    public async Task LeavesDocumentUnchangedIfDocumentContainsSyntaxErrorsIfVerifyOnSave() {
      var source = @"
function GetConstant() int {
  1
}".Trim();
      await SetUp(new Dictionary<string, string>() {
        { $"{DocumentOptions.Section}:{nameof(DocumentOptions.Verify)}", nameof(AutoVerification.OnSave) }
      });
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var openedDocument = await Documents.GetDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(openedDocument);
      await client.SaveDocumentAndWaitAsync(documentItem, CancellationToken);
      var savedDocument = await Documents.GetDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(savedDocument);
      Assert.AreSame(openedDocument, savedDocument);
    }

    [TestMethod]
    public async Task LeavesDocumentUnchangedIfDocumentContainsSemanticErrorsIfVerifyOnSave() {
      var source = @"
function GetConstant(): int {
  d
}".Trim();
      await SetUp(new Dictionary<string, string>() {
        { $"{DocumentOptions.Section}:{nameof(DocumentOptions.Verify)}", nameof(AutoVerification.OnSave) }
      });
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var openedDocument = await Documents.GetDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(openedDocument);
      await client.SaveDocumentAndWaitAsync(documentItem, CancellationToken);
      var savedDocument = await Documents.GetDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(savedDocument);
      Assert.AreSame(openedDocument, savedDocument);
    }

    [TestMethod]
    public async Task UpdatesFlawlessDocumentIfVerifyOnSave() {
      var source = @"
function GetConstant(): int {
  1
}".Trim();
      await SetUp(new Dictionary<string, string>() {
        { $"{DocumentOptions.Section}:{nameof(DocumentOptions.Verify)}", nameof(AutoVerification.OnSave) }
      });
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var openedDocument = await Documents.GetDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(openedDocument);
      await client.SaveDocumentAndWaitAsync(documentItem, CancellationToken);
      var savedDocument = await Documents.GetVerifiedDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(savedDocument);
      Assert.AreNotSame(openedDocument, savedDocument);
    }

    [TestMethod]
    public async Task VerificationErrorsAreCapturedIfVerifyOnSave() {
      var source = @"
method DoIt() {
  assert false;
}".Trim();
      await SetUp(new Dictionary<string, string>() {
        { $"{DocumentOptions.Section}:{nameof(DocumentOptions.Verify)}", nameof(AutoVerification.OnSave) }
      });
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await client.SaveDocumentAndWaitAsync(documentItem, CancellationToken);
      var document = await Documents.GetVerifiedDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      Assert.AreEqual(1, document.Errors.ErrorCount);
      var message = document.Errors.GetDiagnostics(documentItem.Uri)[0];
      Assert.AreEqual(MessageSource.Verifier.ToString(), message.Source);
    }
  }
}
