using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.Extensions.Configuration;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.JsonRpc;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various {
  [TestClass]
  public class VerificationNotificationTest : DafnyLanguageServerTestBase {
    private ILanguageClient _client;
    private TestNotificationReceiver _notificationReceiver;
    private IDictionary<string, string> _configuration;

    [TestInitialize]
    public Task SetUp() => SetUp(null);

    public async Task SetUp(IDictionary<string, string> configuration) {
      _configuration = configuration;
      _notificationReceiver = new TestNotificationReceiver();
      _client = await InitializeClient(options => {
        options
          .AddHandler(DafnyRequestNames.VerificationStarted, NotificationHandler.For<VerificationStartedParams>(_notificationReceiver.StatusReceived))
          .AddHandler(DafnyRequestNames.VerificationCompleted, NotificationHandler.For<VerificationCompletedParams>(_notificationReceiver.StatusReceived));
      });
    }

    protected override IConfiguration CreateConfiguration() {
      return _configuration == null
        ? base.CreateConfiguration()
        : new ConfigurationBuilder().AddInMemoryCollection(_configuration).Build();
    }

    [TestMethod]
    public async Task VerifyingDocumentWithoutErrorsSendsActivityAndVerifiedStatus() {
      var source = @"
method Abs(x: int) returns (y: int)
    ensures y >= 0
{
  if x < 0 {
    return -x;
  }
  return x;
}
".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var started = (VerificationStartedParams)await _notificationReceiver.AwaitNextPublishDiagnosticsAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, started.Uri);
      Assert.AreEqual(documentItem.Version, started.Version);
      var completed = (VerificationCompletedParams)await _notificationReceiver.AwaitNextPublishDiagnosticsAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, completed.Uri);
      Assert.AreEqual(documentItem.Version, completed.Version);
      Assert.IsTrue(completed.Verified);
    }

    [TestMethod]
    public async Task VerifyingDocumentWithErrorsSendsActivityAndNotVerifiedStatus() {
      var source = @"
method Abs(x: int) returns (y: int)
    ensures y >= 0
{
  return x;
}
".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var started = (VerificationStartedParams)await _notificationReceiver.AwaitNextPublishDiagnosticsAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, started.Uri);
      Assert.AreEqual(documentItem.Version, started.Version);
      var completed = (VerificationCompletedParams)await _notificationReceiver.AwaitNextPublishDiagnosticsAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, completed.Uri);
      Assert.AreEqual(documentItem.Version, completed.Version);
      Assert.IsFalse(completed.Verified);
    }

    public class TestNotificationReceiver {
      private readonly SemaphoreSlim _availableDiagnostics = new(0);
      private readonly ConcurrentQueue<VerificationParams> _diagnostics = new();

      public void StatusReceived(VerificationParams request) {
        _diagnostics.Enqueue(request);
        _availableDiagnostics.Release();
      }

      public async Task<VerificationParams> AwaitNextPublishDiagnosticsAsync(CancellationToken cancellationToken) {
        await _availableDiagnostics.WaitAsync(cancellationToken);
        if(_diagnostics.TryDequeue(out var diagnostics)) {
          return diagnostics;
        }
        throw new System.InvalidOperationException("got a signal for a received diagnostic but it was not present in the queue");
      }
    }
  }
}
