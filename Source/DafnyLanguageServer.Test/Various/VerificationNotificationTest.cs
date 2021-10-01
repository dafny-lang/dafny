using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.Language;
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
    private const int MaxTestExecutionTimeMs = 10000;

    private ILanguageClient client;
    private TestNotificationReceiver notificationReceiver;
    private IDictionary<string, string> configuration;

    [TestInitialize]
    public Task SetUp() => SetUp(null);

    public async Task SetUp(IDictionary<string, string> configuration) {
      this.configuration = configuration;
      notificationReceiver = new TestNotificationReceiver();
      client = await InitializeClient(options => {
        options
          .AddHandler(DafnyRequestNames.CompilationStatus, NotificationHandler.For<CompilationStatusParams>(notificationReceiver.StatusReceived));
      });
    }

    protected override IConfiguration CreateConfiguration() {
      return configuration == null
        ? base.CreateConfiguration()
        : new ConfigurationBuilder().AddInMemoryCollection(configuration).Build();
    }

    [TestMethod, Timeout(MaxTestExecutionTimeMs)]
    public async Task DocumentWithParserErrorsSendsParsingFailedStatus() {
      var source = @"
method Abs(x: int) returns (y: int)
    ensures y >= 0
{
  return x
}
".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var started = await notificationReceiver.AwaitNextCompilationStatusAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, started.Uri);
      Assert.AreEqual(documentItem.Version, started.Version);
      Assert.AreEqual(CompilationStatus.ParsingFailed, started.Status);

      // We re-send the same erroneous document again to check that we don't have a CompilationSucceeded event queued.
      client.OpenDocument(CreateTestDocument(source, "Test2.dfy"));
      var queueRemainder = await notificationReceiver.AwaitNextCompilationStatusAsync(CancellationToken);
      Assert.AreEqual(CompilationStatus.ParsingFailed, queueRemainder.Status);
    }

    [TestMethod, Timeout(MaxTestExecutionTimeMs)]
    public async Task DocumentWithResolverErrorsSendsResolutionFailedStatus() {
      var source = @"
method Abs(x: int) returns (y: int)
    ensures y >= 0
{
  return z;
}
".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var started = await notificationReceiver.AwaitNextCompilationStatusAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, started.Uri);
      Assert.AreEqual(documentItem.Version, started.Version);
      Assert.AreEqual(CompilationStatus.ResolutionFailed, started.Status);

      // We re-send the same erroneous document again to check that we don't have a CompilationSucceeded event queued.
      client.OpenDocument(CreateTestDocument(source, "Test2.dfy"));
      var queueRemainder = await notificationReceiver.AwaitNextCompilationStatusAsync(CancellationToken);
      Assert.AreEqual(CompilationStatus.ResolutionFailed, queueRemainder.Status);
    }

    [TestMethod, Timeout(MaxTestExecutionTimeMs)]
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
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var compilation = await notificationReceiver.AwaitNextCompilationStatusAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, compilation.Uri);
      Assert.AreEqual(documentItem.Version, compilation.Version);
      Assert.AreEqual(CompilationStatus.CompilationSucceeded, compilation.Status);
      var started = await notificationReceiver.AwaitNextCompilationStatusAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, started.Uri);
      Assert.AreEqual(documentItem.Version, started.Version);
      Assert.AreEqual(CompilationStatus.VerificationStarted, started.Status);
      var completed = await notificationReceiver.AwaitNextCompilationStatusAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, completed.Uri);
      Assert.AreEqual(documentItem.Version, completed.Version);
      Assert.AreEqual(CompilationStatus.VerificationSucceeded, completed.Status);
    }

    [TestMethod, Timeout(MaxTestExecutionTimeMs)]
    public async Task DocumentWithOnlyVerifierErrorsSendsCompilationSucceededVerificationStartedAndVerificationFailedStatuses() {
      var source = @"
method Abs(x: int) returns (y: int)
    ensures y >= 0
{
  return x;
}
".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var compilation = await notificationReceiver.AwaitNextCompilationStatusAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, compilation.Uri);
      Assert.AreEqual(documentItem.Version, compilation.Version);
      Assert.AreEqual(CompilationStatus.CompilationSucceeded, compilation.Status);
      var started = await notificationReceiver.AwaitNextCompilationStatusAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, started.Uri);
      Assert.AreEqual(documentItem.Version, started.Version);
      Assert.AreEqual(CompilationStatus.VerificationStarted, started.Status);
      var completed = await notificationReceiver.AwaitNextCompilationStatusAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, completed.Uri);
      Assert.AreEqual(documentItem.Version, completed.Version);
      Assert.AreEqual(CompilationStatus.VerificationFailed, completed.Status);
    }

    [TestMethod, Timeout(MaxTestExecutionTimeMs)]
    public async Task DocumentWithOnlyCodedVerifierTimeoutSendsCompilationSucceededVerificationStartedAndVerificationFailedStatuses() {
      var source = @"
lemma {:timeLimit 3} SquareRoot2NotRational(p: nat, q: nat)
  requires p > 0 && q > 0
  ensures (p * p) !=  2 * (q * q)
{ 
  if (p * p) ==  2 * (q * q) {
    calc == {
      (2 * q - p) * (2 * q - p);
      4 * q * q + p * p - 4 * p * q;
      {assert 2 * q * q == p * p;}
      2 * q * q + 2 * p * p - 4 * p * q;
      2 * (p - q) * (p - q);
    }
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var compilation = await notificationReceiver.AwaitNextCompilationStatusAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, compilation.Uri);
      Assert.AreEqual(documentItem.Version, compilation.Version);
      Assert.AreEqual(CompilationStatus.CompilationSucceeded, compilation.Status);
      var started = await notificationReceiver.AwaitNextCompilationStatusAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, started.Uri);
      Assert.AreEqual(documentItem.Version, started.Version);
      Assert.AreEqual(CompilationStatus.VerificationStarted, started.Status);
      var completed = await notificationReceiver.AwaitNextCompilationStatusAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, completed.Uri);
      Assert.AreEqual(documentItem.Version, completed.Version);
      Assert.AreEqual(CompilationStatus.VerificationFailed, completed.Status);
    }

    [TestMethod, Timeout(MaxTestExecutionTimeMs)]
    public async Task DocumentWithOnlyConfiguredVerifierTimeoutSendsCompilationSucceededVerificationStartedAndVerificationFailedStatuses() {
      var source = @"
lemma SquareRoot2NotRational(p: nat, q: nat)
  requires p > 0 && q > 0
  ensures (p * p) !=  2 * (q * q)
{ 
  if (p * p) ==  2 * (q * q) {
    calc == {
      (2 * q - p) * (2 * q - p);
      4 * q * q + p * p - 4 * p * q;
      {assert 2 * q * q == p * p;}
      2 * q * q + 2 * p * p - 4 * p * q;
      2 * (p - q) * (p - q);
    }
  }
}".TrimStart();
      await SetUp(new Dictionary<string, string>() {
        { $"{VerifierOptions.Section}:{nameof(VerifierOptions.TimeLimit)}", "3" }
      });
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var compilation = await notificationReceiver.AwaitNextCompilationStatusAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, compilation.Uri);
      Assert.AreEqual(documentItem.Version, compilation.Version);
      Assert.AreEqual(CompilationStatus.CompilationSucceeded, compilation.Status);
      var started = await notificationReceiver.AwaitNextCompilationStatusAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, started.Uri);
      Assert.AreEqual(documentItem.Version, started.Version);
      Assert.AreEqual(CompilationStatus.VerificationStarted, started.Status);
      var completed = await notificationReceiver.AwaitNextCompilationStatusAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, completed.Uri);
      Assert.AreEqual(documentItem.Version, completed.Version);
      Assert.AreEqual(CompilationStatus.VerificationFailed, completed.Status);
    }

    public class TestNotificationReceiver {
      private readonly SemaphoreSlim availableStatuses = new(0);
      private readonly ConcurrentQueue<CompilationStatusParams> compilationStatuses = new();

      public void StatusReceived(CompilationStatusParams request) {
        compilationStatuses.Enqueue(request);
        availableStatuses.Release();
      }

      public async Task<CompilationStatusParams> AwaitNextCompilationStatusAsync(CancellationToken cancellationToken) {
        await availableStatuses.WaitAsync(cancellationToken);
        if (compilationStatuses.TryDequeue(out var diagnostics)) {
          return diagnostics;
        }
        throw new System.InvalidOperationException("got a signal for a received diagnostic but it was not present in the queue");
      }
    }
  }
}
