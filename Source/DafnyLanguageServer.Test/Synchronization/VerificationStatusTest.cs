using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Workspace;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;
using Xunit.Abstractions;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization;

public class VerificationStatusTest : ClientBasedLanguageServerTest {

  [Fact]
  public async Task ParentModuleProjectFileVerification() {

    await SetUp(options => {
      options.Set(ProjectManager.Verification, VerifyOnMode.Never);
    });
    var directory = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName());
    Directory.CreateDirectory(directory);
    await File.WriteAllTextAsync(Path.Combine(directory, "dfyconfig.toml"), "");
    await File.WriteAllTextAsync(Path.Combine(directory, "a.dfy"), "module A {}");
    var b = CreateAndOpenTestDocument("module A.B { \n  method Test() { assert true; }\n}", Path.Combine(directory, "b.dfy"));

    var methodHeader = new Position(1, 11);
    verificationStatusReceiver.GetLatestAndClearQueue(_ => true);
    await client.RunSymbolVerification(new TextDocumentIdentifier(b.Uri), methodHeader, CancellationToken);
    var result = await WaitUntilAllStatusAreCompleted(b);
    Assert.Equal(PublishedVerificationStatus.Correct, result.NamedVerifiables[0].Status);
  }

  /// <summary>
  /// The client does not correctly migrate symbolStatus information,
  /// so we have to republish it if the positions change.
  /// </summary>
  [Fact]
  public async Task NoClientSideMigrationOfCanVerifies() {
    var source = @"const x := 3".TrimStart();

    var documentA = await CreateOpenAndWaitForResolve(source);
    var status = await WaitUntilAllStatusAreCompleted(documentA);
    Assert.Equal(1, status.NamedVerifiables.Count);
    ApplyChange(ref documentA, new Range(0, 0, 0, 12), "");
    var status2 = await WaitUntilAllStatusAreCompleted(documentA);
    Assert.Equal(0, status2.NamedVerifiables.Count);
  }

  [Fact]
  public async Task DoNotMigrateWrongUri() {
    var sourceA = @"
method NotAffectedByChange() {
  assert false;
}
".TrimStart();

    var sourceB = @"
// 1
// 2
// 3
method ShouldNotBeAffectedByChange() {
  assert false;
}
".TrimStart();

    var directory = Path.GetRandomFileName();
    await CreateOpenAndWaitForResolve("", Path.Combine(directory, DafnyProject.FileName));
    var documentA = await CreateOpenAndWaitForResolve(sourceA, Path.Combine(directory, "sourceA.dfy"));
    await WaitUntilAllStatusAreCompleted(documentA);
    var documentB = await CreateOpenAndWaitForResolve(sourceB, Path.Combine(directory, "sourceB.dfy"));
    await WaitUntilAllStatusAreCompleted(documentB);
    ApplyChange(ref documentA, new Range(3, 0, 3, 0), "// change\n");
    await AssertNoVerificationStatusIsComing(documentB, CancellationToken);
  }

  [Fact]
  public async Task ANoopChangeWillCauseVerificationToTriggerAgain() {
    var source = @"
method WillVerify() {
  assert false;
}
".TrimStart();

    var document = await CreateOpenAndWaitForResolve(source);
    await WaitForStatus(null, PublishedVerificationStatus.Error, CancellationToken, document);
    ApplyChange(ref document, new Range(3, 0, 3, 0), "//change comment\n");
    await WaitForStatus(null, PublishedVerificationStatus.Error, CancellationToken, document);
  }

  [Fact]
  public async Task TryingToVerifyShowsUpAsQueued() {
    var source = @"
method Foo() returns (x: int) ensures x / 2 == 1; {
  return 2;
}

method Bar() returns (x: int) ensures x / 2 == 1; {
  return 2;
}

method Zap() returns (x: int) ensures x / 2 == 1; {
  return 2;
}".TrimStart();
    await SetUp(options => {
      options.Set(ProjectManager.Verification, VerifyOnMode.Never);
    });
    var documentItem1 = await CreateOpenAndWaitForResolve(source, "PreparingVerificationShowsUpAsAllQueued.dfy");
    _ = client.RunSymbolVerification(documentItem1, new Position(0, 7), CancellationToken);
    _ = client.RunSymbolVerification(documentItem1, new Position(4, 7), CancellationToken);
    while (true) {
      CancellationToken.ThrowIfCancellationRequested();
      var status = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
      if (status.NamedVerifiables.Count(v => v.Status == PublishedVerificationStatus.Queued) == 2) {
        Assert.Contains(status.NamedVerifiables, v => v.Status == PublishedVerificationStatus.Stale);
        break;
      }

      if (status.NamedVerifiables.All(v => v.Status >= PublishedVerificationStatus.Error)) {
        Assert.Fail("Finished without getting to a dual queued state");
      }
    }

    while (true) {
      CancellationToken.ThrowIfCancellationRequested();
      var status = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
      if (status.NamedVerifiables.Count(v => v.Status == PublishedVerificationStatus.Stale) > 1) {
        Assert.Fail("May not become stale after both being queued. ");
      }

      if (status.NamedVerifiables.Count(v => v.Status >= PublishedVerificationStatus.Error) == 2) {
        return;
      }
    }
  }

  [Fact]
  public async Task RunWithMultipleSimilarDocuments() {
    var source = @"
method Foo() returns (x: int) ensures x / 2 == 1; {
  return 2;
}".TrimStart();
    await SetUp(options => {
      options.Set(ProjectManager.Verification, VerifyOnMode.Never);
    });
    var directory = GetFreshTempPath();
    await CreateOpenAndWaitForResolve("", Path.Combine(directory, DafnyProject.FileName));
    var documentItem1 = await CreateOpenAndWaitForResolve(source, Path.Combine(directory, "RunWithMultipleDocuments1.dfy"));
    var documentItem2 = await CreateOpenAndWaitForResolve(source.Replace("Foo", "Bar"), Path.Combine(directory, "RunWithMultipleDocuments2.dfy"));

    var fooRange = new Range(0, 7, 0, 10);
    await client.RunSymbolVerification(documentItem1, fooRange.Start, CancellationToken);

    await WaitForStatus(fooRange, PublishedVerificationStatus.Correct, CancellationToken, documentItem1);

    await client.RunSymbolVerification(documentItem2, fooRange.Start, CancellationToken);
    await WaitForStatus(fooRange, PublishedVerificationStatus.Correct, CancellationToken, documentItem2);
  }

  [Fact]
  public async Task AssertlessMethodBecomesCorrect() {
    var source = @"
method Foo() {
}";
    var documentItem = CreateTestDocument(source, "AssertlessMethodBecomesCorrect.dfy");
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var fooSymbol = (await RequestDocumentSymbol(documentItem)).Single();
    await WaitForStatus(fooSymbol.SelectionRange, PublishedVerificationStatus.Correct, CancellationToken);
  }

  [Fact]
  public async Task VerifyPositionFromFile1AndUriFromFile2WherePrefixModuleIsInBothFiles() {
    var source = @"
module A.B.C {
  method Foo() returns (x: int) ensures x == 2 {
    return 2;
  }
}".TrimStart();

    var source2 = @"
include ""A.dfy""
module A.B.D {
  method Foo() returns (x: int) ensures x == 2 {
    return 2;
  }
}".TrimStart();
    await SetUp(options => {
      options.Set(ProjectManager.Verification, VerifyOnMode.Never);
      options.Set(CommonOptionBag.VerifyIncludedFiles, true);

    });
    var directory = GetFreshTempPath();
    var documentItem1 = CreateTestDocument(source, Path.Combine(directory, "A.dfy"));
    await client.OpenDocumentAndWaitAsync(documentItem1, CancellationToken);
    var documentItem2 = CreateTestDocument(source2, Path.Combine(directory, "B.dfy"));
    await client.OpenDocumentAndWaitAsync(documentItem2, CancellationToken);
    await AssertNoDiagnosticsAreComing(CancellationToken);
    var fooInFileOnePosition = new Position(1, 9);
    var failsBecausePositionAndUriDoNotMatch = await client.RunSymbolVerification(documentItem2, fooInFileOnePosition, CancellationToken);
    Assert.False(failsBecausePositionAndUriDoNotMatch);
  }

  [Fact]
  public async Task ManuallyRunMethodInPrefixModule() {
    var source = @"
module A.B.C {
  method Foo() returns (x: int) ensures x == 2 {
    return 2;
  }
}".TrimStart();
    await SetUp(options => {
      options.Set(ProjectManager.Verification, VerifyOnMode.Never);
    });
    var documentItem = CreateTestDocument(source);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    await AssertNoDiagnosticsAreComing(CancellationToken);
    var runSuccess = await client.RunSymbolVerification(documentItem, new Position(1, 9), CancellationToken);
    Assert.True(runSuccess);
    await WaitForStatus(new Range(1, 9, 1, 12), PublishedVerificationStatus.Correct, CancellationToken);
  }

  [Fact]
  public async Task ManuallyRunMethodWithTwoUnderlyingTasks() {
    var source = @"
method Foo() returns (x: int) ensures x / 2 == 1; {
  return 2;
}";
    await SetUp(options => {
      options.Set(ProjectManager.Verification, VerifyOnMode.Never);
    });
    var documentItem = CreateTestDocument(source, "ManuallyRunMethodWithTwoUnderlyingTasks.dfy");
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var fooSymbol = (await RequestDocumentSymbol(documentItem)).Single();
    var fooPosition = fooSymbol.SelectionRange.Start;
    var runSuccess = await client.RunSymbolVerification(documentItem, fooPosition, CancellationToken);
    Assert.True(runSuccess);
    await WaitForStatus(fooSymbol.SelectionRange, PublishedVerificationStatus.Correct, CancellationToken);
  }

  [Fact]
  public async Task FunctionByMethodIsSeenAsSingleVerifiable() {
    var source = @"
function MultiplyByPlus(x: nat, y: nat): nat {
  x * y
} by method {
  var result: nat := 0;
  for i := 0 to x 
    invariant result == i * y {
    result := result + y;
  }
  return result;
}";
    var documentItem = CreateTestDocument(source, "FunctionByMethodIsSeenAsSingleVerifiable.dfy");
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var header = (await RequestDocumentSymbol(documentItem)).Single().SelectionRange;
    await WaitForStatus(header, PublishedVerificationStatus.Running, CancellationToken);
    await WaitForStatus(header, PublishedVerificationStatus.Correct, CancellationToken);
  }

  [Fact]
  public async Task NoDuplicateStaleMessages() {
    var source = "method m1() { assert false; }";
    var documentItem = CreateTestDocument(source, "NoDuplicateStaleMessages.dfy");
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

    var foundStale = false;
    while (true) {
      var statusNotification = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
      var status = statusNotification.NamedVerifiables.Single().Status;
      if (status >= PublishedVerificationStatus.Error) {
        break;
      }

      if (status == PublishedVerificationStatus.Stale) {
        Assert.False(foundStale);
        foundStale = true;
      }
    }
  }

  [Fact]
  public async Task NoVerificationStatusPublishedForUnparsedDocument() {
    var source = @"
method m1() {
  assert 3 == 55;
}".TrimStart();
    var documentItem = CreateTestDocument(source, "NoVerificationStatusPublishedForUnparsedDocument.dfy");
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

    await WaitUntilAllStatusAreCompleted(documentItem);
    ApplyChange(ref documentItem, new Range(0, 11, 0, 11), "blargh");
    ApplyChange(ref documentItem, new Range(0, 0, 0, 0), "\n");

    await AssertNoVerificationStatusIsComing(documentItem, CancellationToken);

  }

  [Fact]
  public async Task NoVerificationStatusPublishedForUnresolvedDocument() {
    var source = @"
method m1() {
  assert 3 == 55;
}".TrimStart();
    var documentItem = CreateTestDocument(source, "NoVerificationStatusPublishedForUnresolvedDocument.dfy");
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

    var lastStatus = await WaitUntilAllStatusAreCompleted(documentItem);
    ApplyChange(ref documentItem, new Range(1, 9, 1, 10), "foo");
    ApplyChange(ref documentItem, new Range(0, 0, 0, 0), "\n");

    await AssertNoVerificationStatusIsComing(documentItem, CancellationToken);
  }

  [Fact]
  public async Task ManyConcurrentVerificationRuns() {
    var source = @"
method m1() {
  assert fib(10) == 55;
}
method m2() {
  assert fib(10) == 55;
}
method m3() {
  assert fib(10) == 55;
}
method m4() {
  assert fib(10) == 55;
}
method m5() {
  assert fib(1) == 22322231212312;
}
function fib(n: nat): nat {
  if (n <= 1) then n else fib(n - 1) + fib(n - 2)
}".TrimStart();
    await SetUp(options => {
      options.Set(ProjectManager.Verification, VerifyOnMode.Never);
    });
    var documentItem = CreateTestDocument(source, "ManyConcurrentVerificationRuns.dfy");
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

    var m1 = new Position(0, 7);
    var m2 = new Position(3, 7);
    var m3 = new Position(6, 7);
    var m4 = new Position(9, 7);
    var m5 = new Position(12, 7);
    var fib = new Position(15, 9);
    var textDocumentIdentifier = new TextDocumentIdentifier(documentItem.Uri);
    foreach (var position in new List<Position>() { m1, m2, m3, m4, m5, fib }) {
      var _ = client.RunSymbolVerification(textDocumentIdentifier, position, CancellationToken);
    }

    var finalStatus = await WaitUntilAllStatusAreCompleted(documentItem);
    Assert.True(finalStatus.NamedVerifiables.All(s => s.Status >= PublishedVerificationStatus.Error));
  }

  [Fact]
  public async Task MigrateDeletedVerifiableSymbol() {
    var source = @"method Foo() { assert false; }";
    await SetUp(options => {
      options.Set(ProjectManager.Verification, VerifyOnMode.Never);
    });
    var documentItem = CreateTestDocument(source, "MigrateDeletedVerifiableSymbol.dfy");
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

    var translatedStatusBefore = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.Equal(1, translatedStatusBefore.NamedVerifiables.Count);

    // Delete the end of the Foo range, so Foo() becomes F()
    ApplyChange(ref documentItem, new Range(0, 8, 0, 12), "()");

    var translatedStatusAfter1 = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.Equal(0, translatedStatusAfter1.NamedVerifiables.Count);

    var translatedStatusAfter2 = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.Equal(1, translatedStatusAfter2.NamedVerifiables.Count);
  }

  [Fact]
  public async Task ChangeRunSaveWithVerify() {
    await SetUp(options => {
      options.Set(ProjectManager.Verification, VerifyOnMode.Save);
    });
    var source = @"method Foo() { assert true; }
method Bar() { assert false; }";
    var documentItem = CreateTestDocument(source, "ChangeRunSaveWithVerify.dfy");
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    ApplyChange(ref documentItem, new Range(0, 22, 0, 26), "false");
    var methodHeader = new Position(0, 7);
    var startedVerification = await client.RunSymbolVerification(new TextDocumentIdentifier(documentItem.Uri), methodHeader, CancellationToken);
    Assert.True(startedVerification);
    var preSaveDiagnostics = await GetLastDiagnostics(documentItem, allowStale: true);
    Assert.Single(preSaveDiagnostics);
    await client.SaveDocumentAndWaitAsync(documentItem, CancellationToken);
    var lastDiagnostics = await GetLastDiagnostics(documentItem);
    Assert.Equal(2, lastDiagnostics.Length);
  }

  [Fact]
  public async Task MigratedDiagnosticsAfterManualRun() {
    var source = @"method Foo() { assert false; }";
    await SetUp(options => {
      options.Set(ProjectManager.Verification, VerifyOnMode.Never);
    });
    var documentItem = CreateTestDocument(source, "MigratedDiagnosticsAfterManualRun.dfy");
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

    var methodHeader = new Position(0, 7);
    await client.RunSymbolVerification(new TextDocumentIdentifier(documentItem.Uri), methodHeader, CancellationToken);
    await WaitUntilAllStatusAreCompleted(documentItem);

    var beforeChangeDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.Single(beforeChangeDiagnostics);

    ApplyChange(ref documentItem, new Range(0, 0, 0, 0), "\n");

    var afterChangeDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.Single(afterChangeDiagnostics);
  }

  [Fact]
  public async Task ManualRunCancelCancelRunRun() {

    await SetUp(options => {
      options.Set(ProjectManager.Verification, VerifyOnMode.Never);
    });
    var documentItem = CreateTestDocument(SlowToVerify, "ManualRunCancelCancelRunRun.dfy");
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var stale = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.Equal(documentItem.Uri, stale.Uri);
    Assert.Equal(PublishedVerificationStatus.Stale, stale.NamedVerifiables[0].Status);
    await AssertNoVerificationStatusIsComing(documentItem, CancellationToken);

    var methodHeader = new Position(0, 32);
    await client.RunSymbolVerification(new TextDocumentIdentifier(documentItem.Uri), methodHeader, CancellationToken);
    var running0 = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.Equal(documentItem.Uri, running0.Uri);
    Assert.Equal(PublishedVerificationStatus.Queued, running0.NamedVerifiables[0].Status);

    var running1 = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.Equal(PublishedVerificationStatus.Running, running1.NamedVerifiables[0].Status);

    await client.CancelSymbolVerification(new TextDocumentIdentifier(documentItem.Uri), methodHeader, CancellationToken);
    // Do a second cancel to check it doesn't crash.
    await client.CancelSymbolVerification(new TextDocumentIdentifier(documentItem.Uri), methodHeader, CancellationToken);

    var staleAgain = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.Equal(PublishedVerificationStatus.Stale, staleAgain.NamedVerifiables[0].Status);

    var successfulRun = await client.RunSymbolVerification(new TextDocumentIdentifier(documentItem.Uri), methodHeader, CancellationToken);
    Assert.True(successfulRun);
    var range = new Range(0, 31, 0, 53);
    await WaitForStatus(range, PublishedVerificationStatus.Running, CancellationToken);
    await WaitForStatus(range, PublishedVerificationStatus.Error, CancellationToken);

    var failedRun = await client.RunSymbolVerification(new TextDocumentIdentifier(documentItem.Uri), methodHeader, CancellationToken);
    Assert.False(failedRun);
  }

  [Fact]
  public async Task SingleMethodGoesThroughAllPhases() {
    var source = @"method Foo() { assert false; }";

    await SetUp(options => {
      options.Set(ProjectManager.Verification, VerifyOnMode.Save);
    });
    var documentItem = CreateTestDocument(source, "SingleMethodGoesThroughAllPhasesExceptQueued.dfy");
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var stale = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.Equal(PublishedVerificationStatus.Stale, stale.NamedVerifiables[0].Status);
    client.SaveDocument(documentItem);
    var queued = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.Equal(PublishedVerificationStatus.Queued, queued.NamedVerifiables[0].Status);
    var verifying = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.Equal(PublishedVerificationStatus.Running, verifying.NamedVerifiables[0].Status);
    var errored = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.Equal(PublishedVerificationStatus.Error, errored.NamedVerifiables[0].Status);
  }

  [Fact]
  public async Task QueuedMethodGoesThroughAllPhases() {
    var source = @"method Foo() { assert false; }
method Bar() { assert false; }";

    await SetUp(options => {
      options.Set(BoogieOptionBag.Cores, 1U);
    });
    var documentItem = CreateTestDocument(source, "QueuedMethodGoesThroughAllPhases.dfy");
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

    var barRange = new Range(new Position(1, 7), new Position(1, 10));

    await WaitForStatus(barRange, PublishedVerificationStatus.Stale, CancellationToken);
    await WaitForStatus(barRange, PublishedVerificationStatus.Queued, CancellationToken);
    await WaitForStatus(barRange, PublishedVerificationStatus.Running, CancellationToken);
    await WaitForStatus(barRange, PublishedVerificationStatus.Error, CancellationToken);
  }

  [Fact]
  public async Task WhenUsingOnSaveMethodStaysStaleUntilSave() {
    var source = @"method Foo() { assert false; }
";

    await SetUp(options => {
      options.Set(ProjectManager.Verification, VerifyOnMode.Save);
    });
    var documentItem = CreateTestDocument(source, "WhenUsingOnSaveMethodStaysStaleUntilSave.dfy");
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var stale1 = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.Equal(PublishedVerificationStatus.Stale, stale1.NamedVerifiables[0].Status);

    // Send a change to enable getting a new status notification.
    ApplyChange(ref documentItem, new Range(new Position(1, 0), new Position(1, 0)), "\n");

    await client.SaveDocumentAndWaitAsync(documentItem, CancellationToken);

    var queued = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.Equal(PublishedVerificationStatus.Queued, queued.NamedVerifiables[0].Status);
    var running = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.Equal(PublishedVerificationStatus.Running, running.NamedVerifiables[0].Status);

    var errored = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.Equal(PublishedVerificationStatus.Error, errored.NamedVerifiables[0].Status);
  }

  [Fact]
  public async Task CachingDoesNotWork() {
    var source = @"method Foo() { assert true; }
method Bar() { assert true; }";

    await SetUp(options => {
      options.Set(BoogieOptionBag.Cores, 1U);
      options.Set(LanguageServer.VerifySnapshots, 1U);
    });

    var documentItem = CreateTestDocument(source, "CachingDoesNotWork.dfy");
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

    await WaitUntilAllStatusAreCompleted(documentItem);

    ApplyChange(ref documentItem, new Range(new Position(1, 22), new Position(1, 26)), "false");

    var stale = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    await AssertNoResolutionErrors(documentItem);

    // Uncomment when caching works
    // Assert.Equal(PublishedVerificationStatus.Correct, correct.NamedVerifiables[0].Status);
    Assert.Equal(PublishedVerificationStatus.Stale, stale.NamedVerifiables[0].Status);
    Assert.True(stale.NamedVerifiables[1].Status < PublishedVerificationStatus.Error);
  }


  [Fact]
  public async Task StatusesOfDifferentImplementationUnderOneNamedVerifiableAreCorrectlyMerged() {
    var source = @"
method NotWellDefined() {
  var x := 3 / 0;
}

method InvalidBody() {
  assert false;
}

method InvalidPostCondition() ensures false {
}
";

    var documentItem = CreateTestDocument(source, "StatusesOfDifferentImplementationUnderOneNamedVerifiableAreCorrectlyMerged.dfy");
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    FileVerificationStatus status;
    do {
      status = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    } while (status.NamedVerifiables.Any(v => v.Status < PublishedVerificationStatus.Error));

    Assert.Equal(3, status.NamedVerifiables.Count);
    Assert.Equal(PublishedVerificationStatus.Error, status.NamedVerifiables[0].Status);
    Assert.Equal(PublishedVerificationStatus.Error, status.NamedVerifiables[1].Status);
    Assert.Equal(PublishedVerificationStatus.Error, status.NamedVerifiables[2].Status);
  }

  [Fact]
  public async Task AllTypesOfNamedVerifiablesAreIdentified() {
    var source = @"
// Should show
datatype Shape = Circle(radius: nat := 3) | Rectangle(length: real, width: real)

trait ThatTrait {
  method MethodWillBeOverriden() returns (x: int) ensures x > 0

  // Show show
  function FunctionWillBeOverriden(): int ensures FunctionWillBeOverriden() > 0
}

class BestInClass extends ThatTrait {
  // Should show
  const thatConst: nat := 3;

  // Should show
  method MethodWillBeOverriden() returns (x: int) ensures x > 2 {
    x := 3;
  }

  // Should show
  function FunctionWillBeOverriden(): int {
    3
  }

}

// Should show
type myNat = x: int | x > 0 witness 1

// Should show
newtype myNewNat = x: int | x > 0 witness 1

// Should show
iterator ThatIterator(x: int) yields (y: int, z: int) 
  ensures y > 0 && z > 0 {
  y := 2;
  z := 3;
  yield;
  y := 1;
  z := 2;
  yield;
}".TrimStart();

    var documentItem = CreateTestDocument(source, "AllTypesOfNamedVerifiablesAreIdentified.dfy");
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    await AssertNoResolutionErrors(documentItem);
    var status = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);

    Assert.Equal(9, status.NamedVerifiables.Count);
    var index = 0;
    Assert.Equal(new Range(1, 17, 1, 23), status.NamedVerifiables[index++].NameRange);
    // This entry doesn't actually have anything to verify, but that's hard to determine so it's shown here.
    Assert.Equal(new Range(4, 9, 4, 30), status.NamedVerifiables[index++].NameRange);
    Assert.Equal(new Range(7, 11, 7, 34), status.NamedVerifiables[index++].NameRange);
    Assert.Equal(new Range(12, 8, 12, 17), status.NamedVerifiables[index++].NameRange);
    Assert.Equal(new Range(15, 9, 15, 30), status.NamedVerifiables[index++].NameRange);
    Assert.Equal(new Range(20, 11, 20, 34), status.NamedVerifiables[index++].NameRange);
    Assert.Equal(new Range(27, 5, 27, 10), status.NamedVerifiables[index++].NameRange);
    Assert.Equal(new Range(30, 8, 30, 16), status.NamedVerifiables[index++].NameRange);
    Assert.Equal(new Range(33, 9, 33, 21), status.NamedVerifiables[index].NameRange);
  }

  [Fact]
  public async Task VerificationStatusNotUpdatedOnResolutionError() {
    var source = @"method Foo() { assert false; }
";
    var documentItem = CreateTestDocument(source, "VerificationStatusNotUpdatedOnResolutionError.dfy");
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    await WaitUntilAllStatusAreCompleted(documentItem);
    ApplyChange(ref documentItem, new Range(1, 0, 1, 0), "Garbage"); // Remove 'm'
    await AssertNoVerificationStatusIsComing(documentItem, CancellationToken);
  }

  [Fact]
  public async Task AddedMethodIsShownBeforeItVerifies() {
    var source = @"method Foo() { assert false; }
";
    var documentItem = CreateTestDocument(source, "AddedMethodIsShownBeforeItVerifies.dfy");
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var status1 = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.Equal(1, status1.NamedVerifiables.Count);
    await WaitUntilAllStatusAreCompleted(documentItem);
    ApplyChange(ref documentItem, new Range(1, 0, 1, 0), "\n" + NeverVerifies); // Remove 'm'
    var status2 = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.Equal(2, status2.NamedVerifiables.Count);
  }

  /// <summary>
  /// The token of refining declarations is set to the token of their base declaration during refinement.
  /// The original source location is no longer available.
  /// Without changing that, we can not show the status of individual refining declarations.
  /// </summary>
  [Fact]
  public async Task RefiningDeclarationStatusIsNotFoldedIntoTheBase() {
    var source = @"
abstract module BaseModule {
  method Foo() returns (x: int) ensures x > 2 
}

module Refinement1 refines BaseModule {
  method Foo() returns (x: int) ensures x > 2 {
    return 3;
  }
}

module Refinement2 refines BaseModule {
  method Foo() returns (x: int) ensures x > 2 {
    return 1;
  }
}".TrimStart();
    var documentItem = CreateTestDocument(source, "RefiningDeclarationStatusIsFoldedIntoTheBase.dfy");
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var status = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);

    Assert.Equal(3, status.NamedVerifiables.Count);
    Assert.Equal(new Range(1, 9, 1, 12), status.NamedVerifiables[0].NameRange);
    Assert.Equal(new Range(5, 9, 5, 12), status.NamedVerifiables[1].NameRange);
    Assert.Equal(new Range(11, 9, 11, 12), status.NamedVerifiables[2].NameRange);
  }

  [Fact]
  public async Task SymbolStatusIsMigrated() {
    var source = @"method Foo() { assert false; }";
    var documentItem = CreateTestDocument(source, "SymbolStatusIsMigrated.dfy");
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    await WaitUntilAllStatusAreCompleted(documentItem);
    ApplyChange(ref documentItem, new Range(0, 0, 0, 0), "\n");
    var migratedRange = new Range(1, 7, 1, 10);

    var runningStatus = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.Equal(migratedRange, runningStatus.NamedVerifiables[0].NameRange);

    var errorStatus = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.Equal(migratedRange, errorStatus.NamedVerifiables[0].NameRange);
  }

  public VerificationStatusTest(ITestOutputHelper output) : base(output) {
  }
}
