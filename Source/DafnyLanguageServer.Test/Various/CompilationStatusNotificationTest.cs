using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using System.Threading.Tasks;
using JetBrains.Annotations;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various {
  [Collection("Sequential Collection")] // Sequential because we saw test failures after switching to parallel execution
  public class CompilationStatusNotificationTest : ClientBasedLanguageServerTest {
    private const int MaxTestExecutionTimeMs = 10000;

    [Fact]
    public async Task MultipleDocuments() {
      var source = @"
method Foo() returns (x: int) ensures x / 2 == 1; {
  return 2;
}".TrimStart();
      await SetUp(options => {
        options.Set(ServerCommand.ProjectMode, true);
      });
      var directory = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName());
      Directory.CreateDirectory(directory);
      await CreateAndOpenTestDocument("", Path.Combine(directory, DafnyProject.FileName));
      var secondFilePath = Path.Combine(directory, "RunWithMultipleDocuments2.dfy");
      await File.WriteAllTextAsync(secondFilePath, source.Replace("Foo", "Bar"));
      var documentItem1 = await CreateAndOpenTestDocument(source, Path.Combine(directory, "RunWithMultipleDocuments1.dfy"));

      var expectedStatuses = new[] {
        CompilationStatus.Parsing, CompilationStatus.ResolutionStarted, CompilationStatus.CompilationSucceeded,
        CompilationStatus.PreparingVerification
      };
      var documents = new[] { documentItem1.Uri, DocumentUri.File(secondFilePath) };
      foreach (var expectedStatus in expectedStatuses) {
        var statuses = new Dictionary<DocumentUri, CompilationStatusParams>();
        foreach (var _ in documents) {
          var statusParams = await compilationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
          statuses.Add(statusParams.Uri, statusParams);
        }
        foreach (var document in documents) {
          var status = statuses[document];
          Assert.Equal(expectedStatus, status.Status);
        }
      }
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
      await AssertProgress(documentItem, CompilationStatus.Parsing);
      await AssertProgress(documentItem, CompilationStatus.ParsingFailed);

      // We re-send the same erroneous document again to check that we don't have a CompilationSucceeded event queued.
      var otherDoc = CreateTestDocument(source, "Test2.dfy");
      client.OpenDocument(otherDoc);
      await AssertProgress(otherDoc, CompilationStatus.Parsing);
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
      await AssertProgress(documentItem, CompilationStatus.Parsing);
      await AssertProgress(documentItem, CompilationStatus.ResolutionStarted);
      await AssertProgress(documentItem, CompilationStatus.ResolutionFailed);

      // We re-send the same erroneous document again to check that we don't have a CompilationSucceeded event queued.
      var otherDoc = CreateTestDocument(source, "Test2.dfy");
      client.OpenDocument(otherDoc);
      await AssertProgress(otherDoc, CompilationStatus.Parsing);
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
      await AssertProgress(documentItem, CompilationStatus.Parsing);
      await AssertProgress(documentItem, CompilationStatus.ResolutionStarted);
      await AssertProgress(documentItem, CompilationStatus.CompilationSucceeded);
    }
    private async Task AssertProgress(TextDocumentItem documentItem, CompilationStatus expectedStatus, [CanBeNull] string expectedMessage = null) {
      var lastResult = await compilationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
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
      await AssertProgress(documentItem, CompilationStatus.Parsing);
      await AssertProgress(documentItem, CompilationStatus.ResolutionStarted);
      await AssertProgress(documentItem, CompilationStatus.CompilationSucceeded);
    }

    [Fact(Timeout = MaxTestExecutionTimeMs)]
    public async Task DocumentWithOnlyCodedVerifierTimeoutSendsCompilationSucceededVerificationStartedAndVerificationFailedStatuses() {
      var documentItem = CreateTestDocument(SlowToVerify);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await AssertProgress(documentItem, CompilationStatus.Parsing);
      await AssertProgress(documentItem, CompilationStatus.ResolutionStarted);
      await AssertProgress(documentItem, CompilationStatus.CompilationSucceeded);
    }

    [Fact(Timeout = MaxTestExecutionTimeMs)]
    public async Task DocumentWithOnlyConfiguredVerifierTimeoutSendsCompilationSucceededVerificationStartedAndVerificationFailedStatuses() {
      await SetUp(options => options.Set(BoogieOptionBag.VerificationTimeLimit, 3U));
      var documentItem = CreateTestDocument(SlowToVerify);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await AssertProgress(documentItem, CompilationStatus.Parsing);
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
      await AssertProgress(documentItem1, CompilationStatus.Parsing);
      await AssertProgress(documentItem1, CompilationStatus.ResolutionStarted);
      await AssertProgress(documentItem1, CompilationStatus.CompilationSucceeded);
      await AssertProgress(documentItem1, CompilationStatus.PreparingVerification);
      var documentItem2 = CreateTestDocument(source, "test_2dfy");
      await client.OpenDocumentAndWaitAsync(documentItem2, CancellationToken);
      await AssertProgress(documentItem2, CompilationStatus.Parsing);
      await AssertProgress(documentItem2, CompilationStatus.ResolutionStarted);
      await AssertProgress(documentItem2, CompilationStatus.CompilationSucceeded);
      await AssertProgress(documentItem2, CompilationStatus.PreparingVerification);
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
      await AssertProgress(documentItem1, CompilationStatus.Parsing);
      await AssertProgress(documentItem1, CompilationStatus.ResolutionStarted);
      await AssertProgress(documentItem1, CompilationStatus.CompilationSucceeded);
      await AssertProgress(documentItem1, CompilationStatus.PreparingVerification);
      var documentItem2 = CreateTestDocument(source, "test_2dfy");
      await client.OpenDocumentAndWaitAsync(documentItem2, CancellationToken);
      await client.SaveDocumentAndWaitAsync(documentItem2, CancellationToken);
      await AssertProgress(documentItem2, CompilationStatus.Parsing);
      await AssertProgress(documentItem2, CompilationStatus.ResolutionStarted);
      await AssertProgress(documentItem2, CompilationStatus.CompilationSucceeded);
      await AssertProgress(documentItem2, CompilationStatus.PreparingVerification);
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
      await AssertProgress(documentItem, CompilationStatus.Parsing);
      await AssertProgress(documentItem, CompilationStatus.ParsingFailed);
    }

    public CompilationStatusNotificationTest(ITestOutputHelper output) : base(output) {
    }
  }
}
