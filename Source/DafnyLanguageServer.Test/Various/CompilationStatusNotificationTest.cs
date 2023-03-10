using System;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.JsonRpc;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using System.Threading.Tasks;
using JetBrains.Annotations;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various {
  [Collection("Sequential Collection")] // Sequential because we saw test failures after switching to parallel execution
  public class CompilationStatusNotificationTest : DafnyLanguageServerTestBase, IAsyncLifetime {
    private const int MaxTestExecutionTimeMs = 10000;

    private ILanguageClient client;
    private TestNotificationReceiver<CompilationStatusParams> notificationReceiver;

    public Task InitializeAsync() {
      return SetUp(null);
    }

    public Task DisposeAsync() {
      return Task.CompletedTask;
    }

    protected async Task SetUp(Action<DafnyOptions> modifyOptions) {
      notificationReceiver = new();
      client = await InitializeClient(options => {
        options
          .AddHandler(DafnyRequestNames.CompilationStatus, NotificationHandler.For<CompilationStatusParams>(notificationReceiver.NotificationReceived));
      }, modifyOptions);
    }

    [Fact(Timeout = MaxTestExecutionTimeMs)]
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
      await AssertProgress(documentItem, CompilationStatus.ResolutionStarted);
      await AssertProgress(documentItem, CompilationStatus.ParsingFailed);

      // We re-send the same erroneous document again to check that we don't have a CompilationSucceeded event queued.
      var otherDoc = CreateTestDocument(source, "Test2.dfy");
      client.OpenDocument(otherDoc);
      await AssertProgress(otherDoc, CompilationStatus.ResolutionStarted);
      await AssertProgress(otherDoc, CompilationStatus.ParsingFailed);
    }

    [Fact(Timeout = MaxTestExecutionTimeMs)]
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
      await AssertProgress(documentItem, CompilationStatus.ResolutionStarted);
      await AssertProgress(documentItem, CompilationStatus.ResolutionFailed);

      // We re-send the same erroneous document again to check that we don't have a CompilationSucceeded event queued.
      var otherDoc = CreateTestDocument(source, "Test2.dfy");
      client.OpenDocument(otherDoc);
      await AssertProgress(otherDoc, CompilationStatus.ResolutionStarted);
      await AssertProgress(otherDoc, CompilationStatus.ResolutionFailed);
    }

    [Fact(Timeout = MaxTestExecutionTimeMs)]
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
      await AssertProgress(documentItem, CompilationStatus.ResolutionStarted);
      await AssertProgress(documentItem, CompilationStatus.CompilationSucceeded);
    }
    private async Task AssertProgress(TextDocumentItem documentItem, CompilationStatus expectedStatus, [CanBeNull] string expectedMessage = null) {
      var lastResult = await notificationReceiver.AwaitNextNotificationAsync(CancellationToken);
      Assert.Equal(documentItem.Uri, lastResult.Uri);
      Assert.Equal(documentItem.Version, lastResult.Version);
      Assert.Equal(expectedStatus, lastResult.Status);
      if (expectedMessage != null) {
        Assert.Equal(expectedMessage, lastResult.Message);
      }
    }

    [Fact(Timeout = MaxTestExecutionTimeMs)]
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
      await AssertProgress(documentItem, CompilationStatus.ResolutionStarted);
      await AssertProgress(documentItem, CompilationStatus.CompilationSucceeded);
    }

    [Fact(Timeout = MaxTestExecutionTimeMs)]
    public async Task DocumentWithOnlyCodedVerifierTimeoutSendsCompilationSucceededVerificationStartedAndVerificationFailedStatuses() {
      var documentItem = CreateTestDocument(SlowToVerify);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await AssertProgress(documentItem, CompilationStatus.ResolutionStarted);
      await AssertProgress(documentItem, CompilationStatus.CompilationSucceeded);
    }

    [Fact(Timeout = MaxTestExecutionTimeMs)]
    public async Task DocumentWithOnlyConfiguredVerifierTimeoutSendsCompilationSucceededVerificationStartedAndVerificationFailedStatuses() {
      await SetUp(options => options.Set(BoogieOptionBag.VerificationTimeLimit, 3U));
      var documentItem = CreateTestDocument(SlowToVerify);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await AssertProgress(documentItem, CompilationStatus.ResolutionStarted);
      await AssertProgress(documentItem, CompilationStatus.CompilationSucceeded);
    }

    [Fact(Timeout = MaxTestExecutionTimeMs)]
    public async Task DocumentLoadWithOnSaveVerificationDoesNotSendVerificationStatuses() {
      var source = @"
method Abs(x: int) returns (y: int)
    ensures y >= 0
{
  return x;
}
".TrimStart();
      await SetUp(options => options.Set(ServerCommand.Verification, VerifyOnMode.Save));

      // We load two documents. If no verification is executed, we should receive each
      // compilation status twice without any verification status inbetween.
      var documentItem1 = CreateTestDocument(source, "test_1.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem1, CancellationToken);
      var documentItem2 = CreateTestDocument(source, "test_2dfy");
      await client.OpenDocumentAndWaitAsync(documentItem2, CancellationToken);

      await AssertProgress(documentItem1, CompilationStatus.ResolutionStarted);
      await AssertProgress(documentItem1, CompilationStatus.CompilationSucceeded);
      await AssertProgress(documentItem2, CompilationStatus.ResolutionStarted);
      await AssertProgress(documentItem2, CompilationStatus.CompilationSucceeded);
    }

    [Fact(Timeout = MaxTestExecutionTimeMs)]
    public async Task DocumentLoadAndSaveWithNeverVerifySendsNoVerificationStatuses() {
      var source = @"
method Abs(x: int) returns (y: int)
    ensures y >= 0
{
  return x;
}
".TrimStart();
      await SetUp(options => options.Set(ServerCommand.Verification, VerifyOnMode.Never));

      // We load two and save two documents. If no verification is executed, we should receive each
      // compilation status twice without any verification status inbetween.
      var documentItem1 = CreateTestDocument(source, "test_1.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem1, CancellationToken);
      await client.SaveDocumentAndWaitAsync(documentItem1, CancellationToken);
      var documentItem2 = CreateTestDocument(source, "test_2dfy");
      await client.OpenDocumentAndWaitAsync(documentItem2, CancellationToken);
      await client.SaveDocumentAndWaitAsync(documentItem2, CancellationToken);
      await AssertProgress(documentItem1, CompilationStatus.ResolutionStarted);
      await AssertProgress(documentItem1, CompilationStatus.CompilationSucceeded);
      await AssertProgress(documentItem2, CompilationStatus.ResolutionStarted);
      await AssertProgress(documentItem2, CompilationStatus.CompilationSucceeded);
    }

    [Fact(Timeout = MaxTestExecutionTimeMs)]
    public async Task MultisetShouldNotCrashParser() {
      var source = @"
    lemma Something(i: int)
    {
      calc {
        multiset
      }
    }";
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await AssertProgress(documentItem, CompilationStatus.ResolutionStarted);
      await AssertProgress(documentItem, CompilationStatus.ParsingFailed);
    }

    public CompilationStatusNotificationTest(ITestOutputHelper output) : base(output)
    {
    }
  }
}
