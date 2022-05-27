using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization;

[TestClass]
public class VerificationStatusTest : ClientBasedLanguageServerTest {

  [TestMethod]
  public async Task SingleMethodGoesThroughAllPhasesExceptQueued() {
    var source = @"method Foo() { assert false; }";

    await SetUp(new Dictionary<string, string> {
      { $"{DocumentOptions.Section}:{nameof(DocumentOptions.Verify)}", nameof(AutoVerification.OnSave) }
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

    await SetUp(new Dictionary<string, string>() {
      { $"{VerifierOptions.Section}:{nameof(VerifierOptions.VcsCores)}", 1.ToString() }
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

    await SetUp(new Dictionary<string, string>() {
      { $"{DocumentOptions.Section}:{nameof(DocumentOptions.Verify)}", nameof(AutoVerification.OnSave) }
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

    var running = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.AreEqual(PublishedVerificationStatus.Running, running.NamedVerifiables[0].Status);

    var errored = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.AreEqual(PublishedVerificationStatus.Error, errored.NamedVerifiables[0].Status);
  }

  [TestMethod]
  public async Task CachingWorks() {
    var source = @"method Foo() { assert true; }
method Bar() { assert true; }";

    await SetUp(new Dictionary<string, string>() {
      { $"{VerifierOptions.Section}:{nameof(VerifierOptions.VcsCores)}", 1.ToString() },
      { $"{VerifierOptions.Section}:{nameof(VerifierOptions.VerifySnapshots)}", 1.ToString() }
    });

    var documentItem = CreateTestDocument(source);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

    await WaitUntilAllStatusAreCompleted();

    await GetLastDiagnostics(documentItem, CancellationToken);
    ApplyChange(ref documentItem, new Range(new Position(1, 22), new Position(1, 26)), "false");
    await AssertNoResolutionErrors(documentItem);
    var correct = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.AreEqual(PublishedVerificationStatus.Correct, correct.NamedVerifiables[0].Status);
    Assert.AreEqual(PublishedVerificationStatus.Stale, correct.NamedVerifiables[1].Status);
  }

  private async Task WaitUntilAllStatusAreCompleted() {
    FileVerificationStatus beforeChangeStatus;
    do {
      beforeChangeStatus = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    } while (beforeChangeStatus.NamedVerifiables.Any(method => method.Status < PublishedVerificationStatus.Error));
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
    var source = @"method Foo() { assert false; }";
    var documentItem = CreateTestDocument(source);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    await WaitUntilAllStatusAreCompleted();
    ApplyChange(ref documentItem, new Range(0, 0, 0, 1), ""); // Remove 'm'
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
    await WaitUntilAllStatusAreCompleted();
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
}