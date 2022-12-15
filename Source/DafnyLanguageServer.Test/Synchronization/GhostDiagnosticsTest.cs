using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.Extensions.Configuration;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.JsonRpc;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization {
  [TestClass]
  public class GhostDiagnosticsTest : ClientBasedLanguageServerTest {

    [TestMethod]
    public async Task OpeningFlawlessDocumentWithoutGhostMarkDoesNotMarkAnything() {
      var source = @"
class C {
  var x: int
  ghost var g: int

  method M()
    modifies this
  {
    var u := g; // this statement is ghost
    // x := x + 1;
    if u == 7 { // this whole if statement is ghost
      u:= u + 2;
    }
    x := x + 1;
    g := x; // this is ghost
    x := x + 1;
    MyLemma(); // this is ghost
  }

  lemma MyLemma()
}".TrimStart();
      await SetUp(options => {
        options.Set(ServerCommand.GhostIndicators, false);
      });
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await GetLastDiagnostics(documentItem, CancellationToken);
      await AssertNoGhostnessIsComing(CancellationToken);
    }

    [TestMethod]
    public async Task OpeningFlawlessDocumentWithGhostMarkStatementsMarksGhostVariableDeclarations() {
      var source = @"
class C {
  var x: int
  ghost var g: int

  method M()
    modifies this
  {
    var u := g; // this statement is ghost
  }

  lemma MyLemma()
}".TrimStart();
      await SetUp(options => {
        options.Set(ServerCommand.GhostIndicators, true);
      });
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var report = await ghostnessReceiver.AwaitNextNotificationAsync(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual("Ghost statement", diagnostics[0].Message);
      Assert.AreEqual(new Range((7, 4), (7, 15)), diagnostics[0].Range);
    }

    [TestMethod]
    public async Task OpeningFlawlessDocumentWithGhostMarkStatementsMarksGhostIfStatements() {
      var source = @"
class C {
  var x: int
  ghost var g: int

  method M()
    modifies this
  {
    if g == 7 { // this whole if statement is ghost
      g := g + 2;
    }
  }

  lemma MyLemma()
}".TrimStart();
      await SetUp(options => {
        options.Set(ServerCommand.GhostIndicators, true);
      });
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var report = await ghostnessReceiver.AwaitNextNotificationAsync(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual("Ghost statement", diagnostics[0].Message);
      Assert.AreEqual(new Range((7, 4), (9, 5)), diagnostics[0].Range);
    }

    [TestMethod]
    public async Task OpeningFlawlessDocumentWithGhostMarkStatementsMarksGhostAssignments() {
      var source = @"
class C {
  var x: int
  ghost var g: int

  method M()
    modifies this
  {
    g := x;
  }

  lemma MyLemma()
}".TrimStart();
      await SetUp(options => {
        options.Set(ServerCommand.GhostIndicators, true);
      });
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var report = await ghostnessReceiver.AwaitNextNotificationAsync(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual("Ghost statement", diagnostics[0].Message);
      Assert.AreEqual(new Range((7, 4), (7, 11)), diagnostics[0].Range);
    }

    [TestMethod]
    public async Task OpeningFlawlessDocumentWithGhostMarkStatementsMarksGhostCalls() {
      var source = @"
class C {
  var x: int
  ghost var g: int

  method M()
    modifies this
  {
    MyLemma();
  }

  lemma MyLemma()
}".TrimStart();
      await SetUp(options => {
        options.Set(ServerCommand.GhostIndicators, true);
      });
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var report = await ghostnessReceiver.AwaitNextNotificationAsync(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual("Ghost statement", diagnostics[0].Message);
      Assert.AreEqual(new Range((7, 4), (7, 14)), diagnostics[0].Range);
    }

    [TestMethod]
    public async Task OpeningFlawlessDocumentWithGhostMarkStatementsMarksAllGhostStatements() {
      var source = @"
class C {
  var x: int
  ghost var g: int

  method M()
    modifies this
  {
    var u := g; // this statement is ghost
    // x := x + 1;
    if u == 7 { // this whole if statement is ghost
      u:= u + 2;
    }
    x := x + 1;
    g := x; // this is ghost
    x := x + 1;
    MyLemma(); // this is ghost
  }

  lemma MyLemma()
}".TrimStart();
      await SetUp(options => {
        options.Set(ServerCommand.GhostIndicators, true);
      });
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var report = await ghostnessReceiver.AwaitNextNotificationAsync(CancellationToken);
      var diagnostics = report.Diagnostics
        .OrderBy(diagnostic => diagnostic.Range.Start)
        .ToArray();
      Assert.AreEqual(4, diagnostics.Length);
      Assert.AreEqual("Ghost statement", diagnostics[0].Message);
      Assert.AreEqual(new Range((7, 4), (7, 15)), diagnostics[0].Range);
      Assert.AreEqual("Ghost statement", diagnostics[1].Message);
      Assert.AreEqual(new Range((9, 4), (11, 5)), diagnostics[1].Range);
      Assert.AreEqual("Ghost statement", diagnostics[2].Message);
      Assert.AreEqual(new Range((13, 4), (13, 11)), diagnostics[2].Range);
      Assert.AreEqual("Ghost statement", diagnostics[3].Message);
      Assert.AreEqual(new Range((15, 4), (15, 14)), diagnostics[3].Range);
    }
  }
}
