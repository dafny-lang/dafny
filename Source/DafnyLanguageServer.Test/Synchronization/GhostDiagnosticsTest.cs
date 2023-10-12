using System.IO;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Language;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization {
  public class GhostDiagnosticsTest : ClientBasedLanguageServerTest {

    [Fact]
    public async Task ExplicitProject() {
      var sourceA = @"
method Foo()
{
  FooLemma(); // this is ghost
}

lemma FooLemma()".TrimStart();
      var sourceB = @"
lemma BarLemma()

method Bar()
{
  BarLemma(); // this is ghost
}".TrimStart();
      await SetUp(options => {
        options.Set(GhostStateDiagnosticCollector.GhostIndicators, true);
      });

      var directory = Path.GetRandomFileName();
      var projectFile = await CreateOpenAndWaitForResolve("", Path.Combine(directory, DafnyProject.FileName));
      var docA = await CreateOpenAndWaitForResolve(sourceA, Path.Combine(directory, "a.dfy"));
      var docB = await CreateOpenAndWaitForResolve(sourceB, Path.Combine(directory, "b.dfy"));

      var report = await ghostnessReceiver.AwaitNextNotificationAsync(CancellationToken);
      var report2 = await ghostnessReceiver.AwaitNextNotificationAsync(CancellationToken);
      Assert.Single(report.Diagnostics);
      Assert.Equal(docA.Uri.ToUri(), report.Uri);
      Assert.Equal(2, report.Diagnostics.Single().Range.Start.Line);

      Assert.Single(report2.Diagnostics);
      Assert.Equal(docB.Uri.ToUri(), report2.Uri);
      Assert.Equal(4, report2.Diagnostics.Single().Range.Start.Line);
    }

    [Fact]
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
        options.Set(GhostStateDiagnosticCollector.GhostIndicators, false);
      });
      var documentItem = CreateTestDocument(source, "OpeningFlawlessDocumentWithoutGhostMarkDoesNotMarkAnything.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await GetLastDiagnostics(documentItem, CancellationToken);
      await AssertNoGhostnessIsComing(CancellationToken);
    }

    [Fact]
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
        options.Set(GhostStateDiagnosticCollector.GhostIndicators, true);
      });
      var documentItem = CreateTestDocument(source, "OpeningFlawlessDocumentWithGhostMarkStatementsMarksGhostVariableDeclarations.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var report = await ghostnessReceiver.AwaitNextNotificationAsync(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.Single(diagnostics);
      Assert.Equal(new Range((7, 4), (7, 15)), diagnostics[0].Range);
    }

    [Fact]
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
        options.Set(GhostStateDiagnosticCollector.GhostIndicators, true);
      });
      var documentItem = CreateTestDocument(source, "OpeningFlawlessDocumentWithGhostMarkStatementsMarksGhostIfStatements.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var report = await ghostnessReceiver.AwaitNextNotificationAsync(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.Single(diagnostics);
      Assert.Equal(new Range((7, 4), (9, 5)), diagnostics[0].Range);
    }

    [Fact]
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
        options.Set(GhostStateDiagnosticCollector.GhostIndicators, true);
      });
      var documentItem = CreateTestDocument(source, "OpeningFlawlessDocumentWithGhostMarkStatementsMarksGhostAssignments.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var report = await ghostnessReceiver.AwaitNextNotificationAsync(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.Single(diagnostics);
      Assert.Equal(new Range((7, 4), (7, 11)), diagnostics[0].Range);
    }

    [Fact]
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
        options.Set(GhostStateDiagnosticCollector.GhostIndicators, true);
      });
      var documentItem = CreateTestDocument(source, "OpeningFlawlessDocumentWithGhostMarkStatementsMarksGhostCalls.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var report = await ghostnessReceiver.AwaitNextNotificationAsync(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.Single(diagnostics);
      Assert.Equal(new Range((7, 4), (7, 14)), diagnostics[0].Range);
    }

    [Fact]
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
        options.Set(GhostStateDiagnosticCollector.GhostIndicators, true);
      });
      var documentItem = CreateTestDocument(source, "OpeningFlawlessDocumentWithGhostMarkStatementsMarksAllGhostStatements.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var report = await ghostnessReceiver.AwaitNextNotificationAsync(CancellationToken);
      var diagnostics = report.Diagnostics
        .OrderBy(diagnostic => diagnostic.Range.Start)
        .ToArray();
      Assert.Equal(4, diagnostics.Length);
      Assert.Equal(new Range((7, 4), (7, 15)), diagnostics[0].Range);
      Assert.Equal(new Range((9, 4), (11, 5)), diagnostics[1].Range);
      Assert.Equal(new Range((13, 4), (13, 11)), diagnostics[2].Range);
      Assert.Equal(new Range((15, 4), (15, 14)), diagnostics[3].Range);
    }

    public GhostDiagnosticsTest(ITestOutputHelper output) : base(output) {
    }
  }
}
