using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit.Abstractions;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization;

[TestClass]
public class VerificationStatusTest : ClientBasedLanguageServerTest {

  [TestMethod]
  public async Task ManuallyRunMethodWithTwoUnderlyingTasks() {
    var source = @"
method Foo() returns (x: int) ensures x / 2 == 1; {
  return 2;
}";
    await SetUp(options => {
      options.Set(ServerCommand.Verification, VerifyOnMode.Never);
    });
    var documentItem = CreateTestDocument(source);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var fooSymbol = (await RequestDocumentSymbol(documentItem)).Single();
    var fooPosition = fooSymbol.SelectionRange.Start;
    var runSuccess = await client.RunSymbolVerification(documentItem, fooPosition, CancellationToken);
    Assert.IsTrue(runSuccess);
    await WaitForStatus(fooSymbol.SelectionRange, PublishedVerificationStatus.Correct, CancellationToken);
  }

  [TestMethod]
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
    var documentItem = CreateTestDocument(source);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var header = (await RequestDocumentSymbol(documentItem)).Single().SelectionRange;
    var diagnostic = await GetLastDiagnostics(documentItem, CancellationToken);
    Assert.AreEqual(0, diagnostic.Length);
    await WaitForStatus(header, PublishedVerificationStatus.Running, CancellationToken);
    await WaitForStatus(header, PublishedVerificationStatus.Correct, CancellationToken);
  }

  [TestMethod]
  public async Task NoDuplicateStaleMessages() {
    var source = "method m1() { assert false; }";
    var documentItem = CreateTestDocument(source);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

    var foundStale = false;
    while (true) {
      var statusNotification = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
      var status = statusNotification.NamedVerifiables.Single().Status;
      if (status >= PublishedVerificationStatus.Error) {
        break;
      }

      if (status == PublishedVerificationStatus.Stale) {
        Assert.IsFalse(foundStale);
        foundStale = true;
      }
    }
  }

  [TestMethod]
  public async Task EmptyVerificationTaskListIsPublishedOnOpenAndChange() {
    var source = "method m1() {}";
    var documentItem = CreateTestDocument(source);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

    DateTime? first = null;
    DateTime? second = null;
    DateTime? third = null;
    try {
      first = DateTime.Now;
      var status1 = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
      Assert.AreEqual(0, status1.NamedVerifiables.Count);

      second = DateTime.Now;
      ApplyChange(ref documentItem, new Range(0, 0, 0, 0), "\n");

      var status2 = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
      Assert.AreEqual(0, status2.NamedVerifiables.Count);
      third = DateTime.Now;
    } catch (OperationCanceledException) {
      Console.WriteLine($"first: {first}, second: {second}, third: {third}");
      Console.WriteLine(verificationStatusReceiver.History.Stringify());
      throw;
    }
  }

  [TestMethod]
  public async Task NoVerificationStatusPublishedForUnparsedDocument() {
    var source = @"
method m1() {
  assert 3 == 55;
}".TrimStart();
    var documentItem = CreateTestDocument(source);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

    await WaitUntilAllStatusAreCompleted(documentItem);
    ApplyChange(ref documentItem, new Range(0, 11, 0, 11), "blargh");
    ApplyChange(ref documentItem, new Range(0, 0, 0, 0), "\n");

    await AssertNoVerificationStatusIsComing(documentItem, CancellationToken);
  }

  [TestMethod]
  public async Task NoVerificationStatusPublishedForUnresolvedDocument() {
    var source = @"
method m1() {
  assert 3 == 55;
}".TrimStart();
    var documentItem = CreateTestDocument(source);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

    await WaitUntilAllStatusAreCompleted(documentItem);
    ApplyChange(ref documentItem, new Range(1, 9, 1, 10), "foo");
    ApplyChange(ref documentItem, new Range(0, 0, 0, 0), "\n");

    await AssertNoVerificationStatusIsComing(documentItem, CancellationToken);
  }

  [TestMethod]
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
      options.Set(ServerCommand.Verification, VerifyOnMode.Never);
    });
    var documentItem = CreateTestDocument(source);
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
    Assert.IsTrue(finalStatus.NamedVerifiables.All(s => s.Status >= PublishedVerificationStatus.Error));
  }

  [TestMethod]
  public async Task MigrateDeletedVerifiableSymbol() {
    var source = @"method Foo() { assert false; }";
    await SetUp(options => {
      options.Set(ServerCommand.Verification, VerifyOnMode.Never);
    });
    var documentItem = CreateTestDocument(source);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

    var translatedStatusBefore = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.AreEqual(1, translatedStatusBefore.NamedVerifiables.Count);

    // Delete the end of the Foo range, so Foo() becomes F()
    ApplyChange(ref documentItem, new Range(0, 8, 0, 12), "()");

    var translatedStatusAfter = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.AreEqual(1, translatedStatusAfter.NamedVerifiables.Count);
  }

  [TestMethod]
  public async Task ChangeRunSaveWithVerify() {
    await SetUp(options => {
      options.Set(ServerCommand.Verification, VerifyOnMode.Save);
    });
    var source = @"method Foo() { assert true; }
method Bar() { assert false; }";
    var documentItem = CreateTestDocument(source);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    ApplyChange(ref documentItem, new Range(0, 22, 0, 26), "false");
    var methodHeader = new Position(0, 7);
    await client.RunSymbolVerification(new TextDocumentIdentifier(documentItem.Uri), methodHeader, CancellationToken);
    await client.WaitForNotificationCompletionAsync(documentItem.Uri, CancellationToken);
    var preSaveDiagnostics = await GetLastDiagnostics(documentItem, CancellationToken);
    Assert.AreEqual(1, preSaveDiagnostics.Length);
    await client.SaveDocumentAndWaitAsync(documentItem, CancellationToken);
    var lastDiagnostics = await GetLastDiagnostics(documentItem, CancellationToken);
    Assert.AreEqual(2, lastDiagnostics.Length);
  }

  [TestMethod]
  public async Task MigratedDiagnosticsAfterManualRun() {
    var source = @"method Foo() { assert false; }";
    await SetUp(options => {
      options.Set(ServerCommand.Verification, VerifyOnMode.Never);
    });
    var documentItem = CreateTestDocument(source);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var initialDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.AreEqual(0, initialDiagnostics.Length);

    var methodHeader = new Position(0, 7);
    await client.RunSymbolVerification(new TextDocumentIdentifier(documentItem.Uri), methodHeader, CancellationToken);
    await WaitUntilAllStatusAreCompleted(documentItem);

    var beforeChangeDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.AreEqual(1, beforeChangeDiagnostics.Length);

    ApplyChange(ref documentItem, new Range(0, 0, 0, 0), "\n");

    var afterChangeDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.AreEqual(1, afterChangeDiagnostics.Length);
  }

  [TestMethod]
  public async Task ManualRunCancelCancelRunRun() {

    await SetUp(options => {
      options.Set(ServerCommand.Verification, VerifyOnMode.Never);
    });
    var documentItem = CreateTestDocument(SlowToVerify);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var stale = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.AreEqual(PublishedVerificationStatus.Stale, stale.NamedVerifiables[0].Status);
    await AssertNoVerificationStatusIsComing(documentItem, CancellationToken);

    var methodHeader = new Position(0, 21);
    await client.RunSymbolVerification(new TextDocumentIdentifier(documentItem.Uri), methodHeader, CancellationToken);
    var running1 = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.AreEqual(PublishedVerificationStatus.Running, running1.NamedVerifiables[0].Status);

    await client.CancelSymbolVerification(new TextDocumentIdentifier(documentItem.Uri), methodHeader, CancellationToken);
    // Do a second cancel to check it doesn't crash.
    await client.CancelSymbolVerification(new TextDocumentIdentifier(documentItem.Uri), methodHeader, CancellationToken);

    var staleAgain = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.AreEqual(PublishedVerificationStatus.Stale, staleAgain.NamedVerifiables[0].Status);

    var successfulRun = await client.RunSymbolVerification(new TextDocumentIdentifier(documentItem.Uri), methodHeader, CancellationToken);
    Assert.IsTrue(successfulRun);
    var range = new Range(0, 21, 0, 43);
    await WaitForStatus(range, PublishedVerificationStatus.Running, CancellationToken);
    await WaitForStatus(range, PublishedVerificationStatus.Error, CancellationToken);

    var failedRun = await client.RunSymbolVerification(new TextDocumentIdentifier(documentItem.Uri), methodHeader, CancellationToken);
    Assert.IsFalse(failedRun);
  }

  [TestMethod]
  public async Task SingleMethodGoesThroughAllPhasesExceptQueued() {
    var source = @"method Foo() { assert false; }";

    await SetUp(options => {
      options.Set(ServerCommand.Verification, VerifyOnMode.Save);
    });
    var documentItem = CreateTestDocument(source);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var diagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.AreEqual(0, diagnostics.Length);
    var stale = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.AreEqual(PublishedVerificationStatus.Stale, stale.NamedVerifiables[0].Status);
    client.SaveDocument(documentItem);
    var verifying = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.AreEqual(PublishedVerificationStatus.Running, verifying.NamedVerifiables[0].Status);
    var errored = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.AreEqual(PublishedVerificationStatus.Error, errored.NamedVerifiables[0].Status);
  }

  [TestMethod]
  public async Task QueuedMethodGoesThroughAllPhases() {
    var source = @"method Foo() { assert false; }
method Bar() { assert false; }";

    await SetUp(options => {
      options.Set(BoogieOptionBag.Cores, 1U);
    });
    var documentItem = CreateTestDocument(source);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

    var resolutionDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.AreEqual(0, resolutionDiagnostics.Length);
    var barRange = new Range(new Position(1, 7), new Position(1, 10));

    await WaitForStatus(barRange, PublishedVerificationStatus.Stale, CancellationToken);
    await WaitForStatus(barRange, PublishedVerificationStatus.Queued, CancellationToken);
    await WaitForStatus(barRange, PublishedVerificationStatus.Running, CancellationToken);
    await WaitForStatus(barRange, PublishedVerificationStatus.Error, CancellationToken);
  }

  [TestMethod]
  public async Task WhenUsingOnSaveMethodStaysStaleUntilSave() {
    var source = @"method Foo() { assert false; }
";

    await SetUp(options => {
      options.Set(ServerCommand.Verification, VerifyOnMode.Save);
    });
    var documentItem = CreateTestDocument(source);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var resolutionDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.AreEqual(0, resolutionDiagnostics.Length);
    var stale = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.AreEqual(PublishedVerificationStatus.Stale, stale.NamedVerifiables[0].Status);

    // Send a change to enable getting a new status notification.
    ApplyChange(ref documentItem, new Range(new Position(1, 0), new Position(1, 0)), "\n");

    await client.SaveDocumentAndWaitAsync(documentItem, CancellationToken);

    var stale2 = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    var running = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.AreEqual(PublishedVerificationStatus.Running, running.NamedVerifiables[0].Status);

    var errored = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.AreEqual(PublishedVerificationStatus.Error, errored.NamedVerifiables[0].Status);
  }

  [TestMethod]
  public async Task CachingWorks() {
    var source = @"method Foo() { assert true; }
method Bar() { assert true; }";

    await SetUp(options => {
      options.Set(BoogieOptionBag.Cores, 1U);
      options.Set(ServerCommand.VerifySnapshots, 1U);
    });

    var documentItem = CreateTestDocument(source);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

    await WaitUntilAllStatusAreCompleted(documentItem);

    ApplyChange(ref documentItem, new Range(new Position(1, 22), new Position(1, 26)), "false");
    await AssertNoResolutionErrors(documentItem);
    var correct = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.AreEqual(PublishedVerificationStatus.Correct, correct.NamedVerifiables[0].Status);
    Assert.IsTrue(correct.NamedVerifiables[1].Status < PublishedVerificationStatus.Error);
  }

  private async Task<FileVerificationStatus> WaitUntilAllStatusAreCompleted(TextDocumentIdentifier documentId) {
    var lastDocument = (DocumentAfterTranslation)(await Documents.GetLastDocumentAsync(documentId));
    var symbols = lastDocument!.ImplementationIdToView.Select(id => id.Key.NamedVerificationTask).ToHashSet();
    FileVerificationStatus beforeChangeStatus;
    do {
      beforeChangeStatus = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    } while (beforeChangeStatus.NamedVerifiables.Count != symbols.Count ||
             beforeChangeStatus.NamedVerifiables.Any(method => method.Status < PublishedVerificationStatus.Error));

    return beforeChangeStatus;
  }

  [TestMethod]
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

    var documentItem = CreateTestDocument(source);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    FileVerificationStatus status;
    do {
      status = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    } while (status.NamedVerifiables.Any(v => v.Status < PublishedVerificationStatus.Error));

    Assert.AreEqual(3, status.NamedVerifiables.Count);
    Assert.AreEqual(PublishedVerificationStatus.Error, status.NamedVerifiables[0].Status);
    Assert.AreEqual(PublishedVerificationStatus.Error, status.NamedVerifiables[1].Status);
    Assert.AreEqual(PublishedVerificationStatus.Error, status.NamedVerifiables[2].Status);
  }

  [TestMethod]
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

    var documentItem = CreateTestDocument(source);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    await AssertNoResolutionErrors(documentItem);
    var status = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);

    Assert.AreEqual(8, status.NamedVerifiables.Count);
    Assert.AreEqual(new Range(1, 17, 1, 23), status.NamedVerifiables[0].NameRange);
    Assert.AreEqual(new Range(7, 11, 7, 34), status.NamedVerifiables[1].NameRange);
    Assert.AreEqual(new Range(12, 8, 12, 17), status.NamedVerifiables[2].NameRange);
    Assert.AreEqual(new Range(15, 9, 15, 30), status.NamedVerifiables[3].NameRange);
    Assert.AreEqual(new Range(20, 11, 20, 34), status.NamedVerifiables[4].NameRange);
    Assert.AreEqual(new Range(27, 5, 27, 10), status.NamedVerifiables[5].NameRange);
    Assert.AreEqual(new Range(30, 8, 30, 16), status.NamedVerifiables[6].NameRange);
    Assert.AreEqual(new Range(33, 9, 33, 21), status.NamedVerifiables[7].NameRange);
  }

  [TestMethod]
  public async Task VerificationStatusNotUpdatedOnResolutionError() {
    var source = @"method Foo() { assert false; }
";
    var documentItem = CreateTestDocument(source);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    await WaitUntilAllStatusAreCompleted(documentItem);
    ApplyChange(ref documentItem, new Range(1, 0, 1, 0), "Garbage"); // Remove 'm'
    await AssertNoVerificationStatusIsComing(documentItem, CancellationToken);
  }

  [TestMethod]
  public async Task AddedMethodIsShownBeforeItVerifies() {
    var source = @"method Foo() { assert false; }
";
    var documentItem = CreateTestDocument(source);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var status1 = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.AreEqual(1, status1.NamedVerifiables.Count);
    await WaitUntilAllStatusAreCompleted(documentItem);
    ApplyChange(ref documentItem, new Range(1, 0, 1, 0), "\n" + NeverVerifies); // Remove 'm'
    var status2 = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.AreEqual(2, status2.NamedVerifiables.Count);
  }

  /// <summary>
  /// The token of refining declarations is set to the token of their base declaration during refinement.
  /// The original source location is no longer available.
  /// Without changing that, we can not show the status of individual refining declarations.
  /// </summary>
  [TestMethod]
  public async Task RefiningDeclarationStatusIsFoldedIntoTheBase() {
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
    var documentItem = CreateTestDocument(source);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var status = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);

    Assert.AreEqual(1, status.NamedVerifiables.Count);
    Assert.AreEqual(new Range(1, 9, 1, 12), status.NamedVerifiables[0].NameRange);
  }

  [TestMethod]
  public async Task SymbolStatusIsMigrated() {
    var source = @"method Foo() { assert false; }";
    var documentItem = CreateTestDocument(source);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    await WaitUntilAllStatusAreCompleted(documentItem);
    ApplyChange(ref documentItem, new Range(0, 0, 0, 0), "\n");
    var migratedRange = new Range(1, 7, 1, 10);

    var runningStatus = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.AreEqual(migratedRange, runningStatus.NamedVerifiables[0].NameRange);

    var errorStatus = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.AreEqual(migratedRange, errorStatus.NamedVerifiables[0].NameRange);
  }

  public VerificationStatusTest(ITestOutputHelper output) : base(output)
  {
  }
}
