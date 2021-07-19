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
          .AddHandler(DafnyRequestNames.CompilationStatus, NotificationHandler.For<CompilationStatusParams>(_notificationReceiver.StatusReceived));
      });
    }

    protected override IConfiguration CreateConfiguration() {
      return _configuration == null
        ? base.CreateConfiguration()
        : new ConfigurationBuilder().AddInMemoryCollection(_configuration).Build();
    }

    [TestMethod, Timeout(5000)]
    public async Task DocumentWithParserErrorsSendsParsingFailedStatus() {
      var source = @"
method Abs(x: int) returns (y: int)
    ensures y >= 0
{
  return x
}
".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var started = await _notificationReceiver.AwaitNextCompilationStatusAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, started.Uri);
      Assert.AreEqual(documentItem.Version, started.Version);
      Assert.AreEqual(CompilationStatus.ParsingFailed, started.Status);

      // We re-send the same erroneous document again to check that we don't have a CompilationSucceeded event queued.
      _client.OpenDocument(CreateTestDocument(source, "Test2.dfy"));
      var queueRemainder = await _notificationReceiver.AwaitNextCompilationStatusAsync(CancellationToken);
      Assert.AreEqual(CompilationStatus.ParsingFailed, queueRemainder.Status);
    }

    [TestMethod, Timeout(5000)]
    public async Task DocumentWithResolverErrorsSendsResolutionFailedStatus() {
      var source = @"
method Abs(x: int) returns (y: int)
    ensures y >= 0
{
  return z;
}
".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var started = await _notificationReceiver.AwaitNextCompilationStatusAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, started.Uri);
      Assert.AreEqual(documentItem.Version, started.Version);
      Assert.AreEqual(CompilationStatus.ResolutionFailed, started.Status);

      // We re-send the same erroneous document again to check that we don't have a CompilationSucceeded event queued.
      _client.OpenDocument(CreateTestDocument(source, "Test2.dfy"));
      var queueRemainder = await _notificationReceiver.AwaitNextCompilationStatusAsync(CancellationToken);
      Assert.AreEqual(CompilationStatus.ResolutionFailed, queueRemainder.Status);
    }

    [TestMethod, Timeout(5000)]
    public async Task DocumentWithoutErrorsSendsCompilationSucceededVerificationStartedAndVerificationSucceededStatuses() {
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
      var compilation = await _notificationReceiver.AwaitNextCompilationStatusAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, compilation.Uri);
      Assert.AreEqual(documentItem.Version, compilation.Version);
      Assert.AreEqual(CompilationStatus.CompilationSucceeded, compilation.Status);
      var started = await _notificationReceiver.AwaitNextCompilationStatusAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, started.Uri);
      Assert.AreEqual(documentItem.Version, started.Version);
      Assert.AreEqual(CompilationStatus.VerificationStarted, started.Status);
      var completed = await _notificationReceiver.AwaitNextCompilationStatusAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, completed.Uri);
      Assert.AreEqual(documentItem.Version, completed.Version);
      Assert.AreEqual(CompilationStatus.VerificationSucceeded, completed.Status);
    }

    [TestMethod, Timeout(5000)]
    public async Task DocumentWithOnlyVerifierErrorsSendsCompilationSucceededVerificationStartedAndVerificationFailedStatuses() {
      var source = @"
method Abs(x: int) returns (y: int)
    ensures y >= 0
{
  return x;
}
".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var compilation = await _notificationReceiver.AwaitNextCompilationStatusAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, compilation.Uri);
      Assert.AreEqual(documentItem.Version, compilation.Version);
      Assert.AreEqual(CompilationStatus.CompilationSucceeded, compilation.Status);
      var started = await _notificationReceiver.AwaitNextCompilationStatusAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, started.Uri);
      Assert.AreEqual(documentItem.Version, started.Version);
      Assert.AreEqual(CompilationStatus.VerificationStarted, started.Status);
      var completed = await _notificationReceiver.AwaitNextCompilationStatusAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, completed.Uri);
      Assert.AreEqual(documentItem.Version, completed.Version);
      Assert.AreEqual(CompilationStatus.VerificationFailed, completed.Status);
    }

    public class TestNotificationReceiver {
      private readonly SemaphoreSlim _availableDiagnostics = new(0);
      private readonly ConcurrentQueue<CompilationStatusParams> _compilationStatuses = new();

      public void StatusReceived(CompilationStatusParams request) {
        _compilationStatuses.Enqueue(request);
        _availableDiagnostics.Release();
      }

      public async Task<CompilationStatusParams> AwaitNextCompilationStatusAsync(CancellationToken cancellationToken) {
        await _availableDiagnostics.WaitAsync(cancellationToken);
        if(_compilationStatuses.TryDequeue(out var diagnostics)) {
          return diagnostics;
        }
        throw new System.InvalidOperationException("got a signal for a received diagnostic but it was not present in the queue");
      }
    }
  }
}
