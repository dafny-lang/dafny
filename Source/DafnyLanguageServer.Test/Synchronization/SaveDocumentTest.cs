using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Configuration;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization {
  [TestClass]
  public class SaveDocumentTest : DafnyLanguageServerTestBase {
    private ILanguageClient _client;
    private IDictionary<string, string> _configuration;

    [TestInitialize]
    public Task SetUp() => SetUp(null);

    public async Task SetUp(IDictionary<string, string> configuration) {
      _configuration = configuration;
      _client = await InitializeClient();
    }

    protected override IConfiguration CreateConfiguration() {
      return _configuration == null
        ? base.CreateConfiguration()
        : new ConfigurationBuilder().AddInMemoryCollection(_configuration).Build();
    }

    [TestMethod]
    public async Task LeavesDocumentUnchangedIfVerifyOnChange() {
      var source = @"
function GetConstant(): int {
  1
}".Trim();
      var documentItem = CreateTestDocument(source);
      await _client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      Assert.IsTrue(Documents.TryGetDocument(documentItem.Uri, out var openedDocument));
      await _client.SaveDocumentAndWaitAsync(documentItem, CancellationToken);
      Assert.IsTrue(Documents.TryGetDocument(documentItem.Uri, out var savedDocument));
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
      await _client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      Assert.IsTrue(Documents.TryGetDocument(documentItem.Uri, out var openedDocument));
      await _client.SaveDocumentAndWaitAsync(documentItem, CancellationToken);
      Assert.IsTrue(Documents.TryGetDocument(documentItem.Uri, out var savedDocument));
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
      await _client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      Assert.IsTrue(Documents.TryGetDocument(documentItem.Uri, out var openedDocument));
      await _client.SaveDocumentAndWaitAsync(documentItem, CancellationToken);
      Assert.IsTrue(Documents.TryGetDocument(documentItem.Uri, out var savedDocument));
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
      await _client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      Assert.IsTrue(Documents.TryGetDocument(documentItem.Uri, out var openedDocument));
      await _client.SaveDocumentAndWaitAsync(documentItem, CancellationToken);
      Assert.IsTrue(Documents.TryGetDocument(documentItem.Uri, out var savedDocument));
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
      await _client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      Assert.IsTrue(Documents.TryGetDocument(documentItem.Uri, out var openedDocument));
      await _client.SaveDocumentAndWaitAsync(documentItem, CancellationToken);
      Assert.IsTrue(Documents.TryGetDocument(documentItem.Uri, out var savedDocument));
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
      _client.OpenDocument(documentItem);
      await _client.SaveDocumentAndWaitAsync(documentItem, CancellationToken);
      Assert.IsTrue(Documents.TryGetDocument(documentItem.Uri, out var document));
      Assert.AreEqual(1, document.Errors.ErrorCount);
      var message = document.Errors.Diagnostics.First().Value[0];
      Assert.AreEqual(MessageSource.Other.ToString(), message.Source);
    }
  }
}
