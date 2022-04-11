using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.Extensions.Configuration;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.JsonRpc;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using System.Collections.Generic;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various {
  [TestClass]
  public class CompilationStatusNotificationTest : DafnyLanguageServerTestBase {
    private const int MaxTestExecutionTimeMs = 10000;

    private ILanguageClient client;
    private TestNotificationReceiver<CompilationStatusParams> notificationReceiver;
    private IDictionary<string, string> configuration;

    [TestInitialize]
    public Task SetUp() => SetUp(null);

    public async Task SetUp(IDictionary<string, string> configuration) {
      this.configuration = configuration;
      notificationReceiver = new();
      client = await InitializeClient(options => {
        options
          .AddHandler(DafnyRequestNames.CompilationStatus, NotificationHandler.For<CompilationStatusParams>(notificationReceiver.NotificationReceived));
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
      var started = await notificationReceiver.AwaitNextNotificationAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, started.Uri);
      Assert.AreEqual(documentItem.Version, started.Version);
      Assert.AreEqual(CompilationStatus.ParsingFailed, started.Status);

      // We re-send the same erroneous document again to check that we don't have a CompilationSucceeded event queued.
      client.OpenDocument(CreateTestDocument(source, "Test2.dfy"));
      var queueRemainder = await notificationReceiver.AwaitNextNotificationAsync(CancellationToken);
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
      var started = await notificationReceiver.AwaitNextNotificationAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, started.Uri);
      Assert.AreEqual(documentItem.Version, started.Version);
      Assert.AreEqual(CompilationStatus.ResolutionFailed, started.Status);

      // We re-send the same erroneous document again to check that we don't have a CompilationSucceeded event queued.
      client.OpenDocument(CreateTestDocument(source, "Test2.dfy"));
      var queueRemainder = await notificationReceiver.AwaitNextNotificationAsync(CancellationToken);
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
      var compilation = await notificationReceiver.AwaitNextNotificationAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, compilation.Uri);
      Assert.AreEqual(documentItem.Version, compilation.Version);
      Assert.AreEqual(CompilationStatus.CompilationSucceeded, compilation.Status);
      var started = await notificationReceiver.AwaitNextNotificationAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, started.Uri);
      Assert.AreEqual(documentItem.Version, started.Version);
      Assert.AreEqual(CompilationStatus.VerificationStarted, started.Status);
      var inprogress = await notificationReceiver.AwaitNextNotificationAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, inprogress.Uri);
      Assert.AreEqual(documentItem.Version, inprogress.Version);
      Assert.AreEqual(CompilationStatus.VerificationStarted, inprogress.Status);
      Assert.AreEqual("Abs", inprogress.Message);
      var completed = await notificationReceiver.AwaitNextNotificationAsync(CancellationToken);
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
      var compilation = await notificationReceiver.AwaitNextNotificationAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, compilation.Uri);
      Assert.AreEqual(documentItem.Version, compilation.Version);
      Assert.AreEqual(CompilationStatus.CompilationSucceeded, compilation.Status);
      var started = await notificationReceiver.AwaitNextNotificationAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, started.Uri);
      Assert.AreEqual(documentItem.Version, started.Version);
      Assert.AreEqual(CompilationStatus.VerificationStarted, started.Status);
      var inprogress = await notificationReceiver.AwaitNextNotificationAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, inprogress.Uri);
      Assert.AreEqual(documentItem.Version, inprogress.Version);
      Assert.AreEqual(CompilationStatus.VerificationStarted, inprogress.Status);
      Assert.AreEqual("Abs", inprogress.Message);
      var completed = await notificationReceiver.AwaitNextNotificationAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, completed.Uri);
      Assert.AreEqual(documentItem.Version, completed.Version);
      Assert.AreEqual(CompilationStatus.VerificationFailed, completed.Status);
    }

    [TestMethod, Timeout(MaxTestExecutionTimeMs)]
    public async Task DocumentWithOnlyCodedVerifierTimeoutSendsCompilationSucceededVerificationStartedAndVerificationFailedStatuses() {
      var documentItem = CreateTestDocument(SlowToVerify);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var compilation = await notificationReceiver.AwaitNextNotificationAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, compilation.Uri);
      Assert.AreEqual(documentItem.Version, compilation.Version);
      Assert.AreEqual(CompilationStatus.CompilationSucceeded, compilation.Status);
      var started = await notificationReceiver.AwaitNextNotificationAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, started.Uri);
      Assert.AreEqual(documentItem.Version, started.Version);
      Assert.AreEqual(CompilationStatus.VerificationStarted, started.Status);
      var inprogress = await notificationReceiver.AwaitNextNotificationAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, inprogress.Uri);
      Assert.AreEqual(documentItem.Version, inprogress.Version);
      Assert.AreEqual(CompilationStatus.VerificationStarted, inprogress.Status);
      Assert.AreEqual("SquareRoot2NotRational", inprogress.Message);
      var completed = await notificationReceiver.AwaitNextNotificationAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, completed.Uri);
      Assert.AreEqual(documentItem.Version, completed.Version);
      Assert.AreEqual(CompilationStatus.VerificationFailed, completed.Status);
    }

    [TestMethod, Timeout(MaxTestExecutionTimeMs)]
    public async Task DocumentWithOnlyConfiguredVerifierTimeoutSendsCompilationSucceededVerificationStartedAndVerificationFailedStatuses() {
      await SetUp(new Dictionary<string, string>() {
        { $"{VerifierOptions.Section}:{nameof(VerifierOptions.TimeLimit)}", "3" }
      });
      var documentItem = CreateTestDocument(SlowToVerify);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var compilation = await notificationReceiver.AwaitNextNotificationAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, compilation.Uri);
      Assert.AreEqual(documentItem.Version, compilation.Version);
      Assert.AreEqual(CompilationStatus.CompilationSucceeded, compilation.Status);
      var started = await notificationReceiver.AwaitNextNotificationAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, started.Uri);
      Assert.AreEqual(documentItem.Version, started.Version);
      Assert.AreEqual(CompilationStatus.VerificationStarted, started.Status);
      var inprogress = await notificationReceiver.AwaitNextNotificationAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, inprogress.Uri);
      Assert.AreEqual(documentItem.Version, inprogress.Version);
      Assert.AreEqual(CompilationStatus.VerificationStarted, inprogress.Status);
      Assert.AreEqual("SquareRoot2NotRational", inprogress.Message);
      var completed = await notificationReceiver.AwaitNextNotificationAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, completed.Uri);
      Assert.AreEqual(documentItem.Version, completed.Version);
      Assert.AreEqual(CompilationStatus.VerificationFailed, completed.Status);
    }

    [TestMethod, Timeout(MaxTestExecutionTimeMs)]
    public async Task DocumentLoadWithOnSaveVerificationDoesNotSendVerificationStatuses() {
      var source = @"
method Abs(x: int) returns (y: int)
    ensures y >= 0
{
  return x;
}
".TrimStart();
      await SetUp(new Dictionary<string, string>() {
        { $"{DocumentOptions.Section}:{nameof(DocumentOptions.Verify)}", nameof(AutoVerification.OnSave) }
      });

      // We load two documents. If no verification is executed, we should receive each
      // compilation status twice without any verification status inbetween.
      var documentItem1 = CreateTestDocument(source, "test_1.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem1, CancellationToken);
      var documentItem2 = CreateTestDocument(source, "test_2dfy");
      await client.OpenDocumentAndWaitAsync(documentItem2, CancellationToken);

      var compilation1 = await notificationReceiver.AwaitNextNotificationAsync(CancellationToken);
      Assert.AreEqual(documentItem1.Uri, compilation1.Uri);
      Assert.AreEqual(documentItem1.Version, compilation1.Version);
      Assert.AreEqual(CompilationStatus.CompilationSucceeded, compilation1.Status);

      var compilation2 = await notificationReceiver.AwaitNextNotificationAsync(CancellationToken);
      Assert.AreEqual(documentItem2.Uri, compilation2.Uri);
      Assert.AreEqual(documentItem2.Version, compilation2.Version);
      Assert.AreEqual(CompilationStatus.CompilationSucceeded, compilation2.Status);
    }

    [TestMethod, Timeout(MaxTestExecutionTimeMs)]
    public async Task DocumentSaveWithOnSaveVerificationSendsVerificationStatuses() {
      var source = @"
method Abs(x: int) returns (y: int)
    ensures y >= 0
{
  return x;
}
".TrimStart();
      await SetUp(new Dictionary<string, string>() {
        { $"{DocumentOptions.Section}:{nameof(DocumentOptions.Verify)}", nameof(AutoVerification.OnSave) }
      });

      var documentItem = CreateTestDocument(source, "test_1.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await client.SaveDocumentAndWaitAsync(documentItem, CancellationToken);

      bool verificationStartedReceived = false;
      bool verificationFailedReceived = false;
      while (!verificationStartedReceived || !verificationFailedReceived) {
        var notification = await notificationReceiver.AwaitNextNotificationAsync(CancellationToken);
        Assert.AreEqual(documentItem.Uri, notification.Uri);
        Assert.AreEqual(documentItem.Version, notification.Version);
        verificationStartedReceived = verificationStartedReceived || notification.Status == CompilationStatus.VerificationStarted;
        verificationFailedReceived = verificationFailedReceived || notification.Status == CompilationStatus.VerificationFailed;
      }
    }

    [TestMethod, Timeout(MaxTestExecutionTimeMs)]
    public async Task DocumentLoadAndSaveWithNeverVerifySendsNoVerificationStatuses() {
      var source = @"
method Abs(x: int) returns (y: int)
    ensures y >= 0
{
  return x;
}
".TrimStart();
      await SetUp(new Dictionary<string, string>() {
        { $"{DocumentOptions.Section}:{nameof(DocumentOptions.Verify)}", nameof(AutoVerification.Never) }
      });

      // We load two and save two documents. If no verification is executed, we should receive each
      // compilation status twice without any verification status inbetween.
      var documentItem1 = CreateTestDocument(source, "test_1.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem1, CancellationToken);
      await client.SaveDocumentAndWaitAsync(documentItem1, CancellationToken);
      var documentItem2 = CreateTestDocument(source, "test_2dfy");
      await client.OpenDocumentAndWaitAsync(documentItem2, CancellationToken);
      await client.SaveDocumentAndWaitAsync(documentItem2, CancellationToken);

      var compilation1 = await notificationReceiver.AwaitNextNotificationAsync(CancellationToken);
      Assert.AreEqual(documentItem1.Uri, compilation1.Uri);
      Assert.AreEqual(documentItem1.Version, compilation1.Version);
      Assert.AreEqual(CompilationStatus.CompilationSucceeded, compilation1.Status);

      var compilation2 = await notificationReceiver.AwaitNextNotificationAsync(CancellationToken);
      Assert.AreEqual(documentItem2.Uri, compilation2.Uri);
      Assert.AreEqual(documentItem2.Version, compilation2.Version);
      Assert.AreEqual(CompilationStatus.CompilationSucceeded, compilation2.Status);
    }
  }
}
