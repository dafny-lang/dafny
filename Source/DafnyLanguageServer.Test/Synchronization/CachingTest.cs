using System.IO;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.DependencyInjection.Extensions;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Server;
using Serilog;
using Serilog.Sinks.InMemory;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization; 

public class CachingTest : ClientBasedLanguageServerTest {
  private InMemorySink sink;

  protected override IServiceCollection ServerOptionsAction(LanguageServerOptions serverOptions) {
    sink = InMemorySink.Instance;
    var logger = new LoggerConfiguration().MinimumLevel.Debug()
      .WriteTo.InMemory().CreateLogger();
    var factory = LoggerFactory.Create(b => b.AddSerilog(logger));
    return base.ServerOptionsAction(serverOptions.WithServices(c => c.Replace(new ServiceDescriptor(typeof(ILoggerFactory), factory))));
  }

  [Fact]
  public async Task GrowingSystemModule() {

    var source = @"
const tuple2 := (3,2)
".TrimStart();

    var testFiles = Path.Combine(Directory.GetCurrentDirectory(), "Synchronization/TestFiles");
    var documentItem = CreateTestDocument(source, Path.Combine(testFiles, "test.dfy"));
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

    await AssertNoDiagnosticsAreComing(CancellationToken);
    ApplyChange(ref documentItem, ((0, 0), (0, 0)), "const tuple3: (int, int, bool) := (1,2,3) \n");
    var diagnostics2 = await GetLastDiagnostics(documentItem, CancellationToken);
    Assert.Single(diagnostics2);
    ApplyChange(ref documentItem, ((0, 0), (0, 0)), "const tuple4: (int, int, bool, bool) := (1,2,3, true) \n");
    var diagnostics3 = await GetLastDiagnostics(documentItem, CancellationToken);
    Assert.Equal(2, diagnostics3.Length);

  }
  [Fact]
  public async Task RootFileChangesTriggerParseAndResolutionCachingAndPruning() {
    var source = @"
include ""./A.dfy""
include ""./B.dfy""
module ModC {
  import ModB
  import ModA
  import ModA.StandalonePrefix.Prefix
  import ModA.FilledWithPrefixes.PrefixContent
  import PrefixModuleInDefaultModule.Content

  const z := ModB.y + 1
  lemma Lem() ensures true {}

  const usage := ModB.calledModAFunction
  const calledModAFunction := ModA.TakesIdentityAndAppliesIt((x, _) => x, 3)
  const tuple2User := ModA.tuple2.0
  const tuple3User := ModA.tuple3.1
  const prefixUser := ModA.FilledWithPrefixes.PrefixContent.x + ModA.StandalonePrefix.Prefix.x + Content.x

  function MatchUser(x: int): int {
    match x {
      case 0 => 1
      case 1 => 2
      case _ => 3
    }
  }
  const matchUserUser := MatchUser(4)
}
".TrimStart();

    var testFiles = Path.Combine(Directory.GetCurrentDirectory(), "Synchronization/TestFiles");
    var documentItem = CreateTestDocument(source, Path.Combine(testFiles, "test.dfy"));
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var hits0 = await WaitAndCountHits();
    Assert.Equal(0, hits0.ParseHits);
    Assert.Equal(0, hits0.ResolveHits);

    async Task<(int ParseHits, int ResolveHits)> WaitAndCountHits() {
      await client.WaitForNotificationCompletionAsync(documentItem.Uri, CancellationToken);
      var parseHits = sink.Snapshot().LogEvents.Count(le => le.MessageTemplate.Text.Contains("Parse cache hit"));
      var resolveHits = sink.Snapshot().LogEvents.Count(le => le.MessageTemplate.Text.Contains("Resolution cache hit"));
      return (parseHits, resolveHits);
    }

    ApplyChange(ref documentItem, ((0, 0), (0, 0)), "// Pointless comment that triggers a reparse\n");
    var hitCount1 = await WaitAndCountHits();
    Assert.Equal(2, hitCount1.ParseHits);
    var modules = new[] {
      "System",
      "ModA", "ModB", "import A (in ModB)",
      "FilledWithPrefixes", "PrefixContent", "StandalonePrefix", "Prefix",
      "PrefixModuleInDefaultModule", "Content",
      "SpreadOverMultipleFiles", "Child1", "Child2"
    };
    Assert.Equal(modules.Length, hitCount1.ResolveHits);

    // Removes the comment and the include and usage of B.dfy, which will prune the cache for B.dfy
    ApplyChange(ref documentItem, ((2, 0), (3, 0)), "");
    var hitCount2 = await WaitAndCountHits();
    Assert.Equal(hitCount1.ParseHits + 1, hitCount2.ParseHits);
    // No resolution was done because the import didn't resolve.
    Assert.Equal(hitCount1.ResolveHits, hitCount2.ResolveHits);

    ApplyChange(ref documentItem, ((0, 0), (0, 0)), "  include \"./B.dfy\"\n");
    var hitCount3 = await WaitAndCountHits();
    // No hit for B.dfy, since it was previously pruned
    Assert.Equal(hitCount2.ParseHits + 1, hitCount3.ParseHits);
    // The resolution cache was pruned after the previous change, so no cache hits here, except for the system module
    Assert.Equal(hitCount2.ResolveHits + 1, hitCount3.ResolveHits);
  }

  /// <summary>
  /// This test uses a file larger than the chunkSize used by CachingParser when chunking files.
  /// </summary>
  [Fact]
  public async Task CachingDetectsStartAndEndAndUriChanges() {
    var source = @"
// Make the file larger
// Make the file larger
// Make the file larger
// Make the file larger
// Make the file larger
// Make the file larger
// Make the file larger
// Make the file larger
// Make the file larger
// Make the file larger
// Make the file larger
// Make the file larger
// Make the file larger
// Make the file larger
// Make the file larger
// Make the file larger
// Make the file larger
// Make the file larger
// Make the file larger
// Make the file larger
// Make the file larger
// Make the file larger
// Make the file larger
// Make the file larger
// Make the file larger
// Make the file larger
// Make the file larger
// Make the file larger
// Make the file larger
// Make the file larger
// Make the file larger
// Make the file larger
// Make the file larger
".TrimStart();

    var firstFile = CreateTestDocument(source, "firstFile");
    await client.OpenDocumentAndWaitAsync(firstFile, CancellationToken);

    async Task<int> WaitAndCountHits() {
      await client.WaitForNotificationCompletionAsync(firstFile.Uri, CancellationToken);
      return sink.Snapshot().LogEvents.Count(le => le.MessageTemplate.Text.Contains("Parse cache hit"));
    }

    var secondFile = CreateTestDocument(source, "secondFile");
    await client.OpenDocumentAndWaitAsync(secondFile, CancellationToken);
    // No hit because Uri has changed
    Assert.Equal(0, await WaitAndCountHits());

    ApplyChange(ref secondFile, ((0, 0), (0, 0)), "// Make the file larger\n");
    // No hit because start of the file has changed
    Assert.Equal(0, await WaitAndCountHits());

    // No hit because end of file has changed
    ApplyChange(ref secondFile, ((19, 0), (19, 0)), "// Make the file larger\n");
    Assert.Equal(0, await WaitAndCountHits());
  }

  [Fact(Skip = "need hashing on modules to work")]
  public async Task ResolutionInSingleFileIsCached() {
    var source = @"
module A {
  var x := 11
}

module B {
  import A;
  var y := A.x + 21;
}
module C {{
  import B;
  var z := B.y + 31;
}}
".TrimStart();

    var testFiles = Path.Combine(Directory.GetCurrentDirectory(), "Synchronization/TestFiles");
    var documentItem = CreateTestDocument(source, Path.Combine(testFiles, "test.dfy"));
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var hits0 = await WaitAndCountHits();
    Assert.Equal(0, hits0);

    async Task<int> WaitAndCountHits() {
      await client.WaitForNotificationCompletionAsync(documentItem.Uri, CancellationToken);
      var parseHits = sink.Snapshot().LogEvents.Count(le => le.MessageTemplate.Text.Contains("Parse cache hit"));
      var resolveHits = sink.Snapshot().LogEvents.Count(le => le.MessageTemplate.Text.Contains("Resolve cache hit"));
      return resolveHits;
    }

    ApplyChange(ref documentItem, ((7, 17), (7, 18)), "22");
    var hitCount1 = await WaitAndCountHits();
    Assert.Equal(1, hitCount1);

    ApplyChange(ref documentItem, ((11, 17), (11, 18)), "32");
    var hitCount2 = await WaitAndCountHits();
    Assert.Equal(hitCount1 + 2, hitCount2);
  }

  [Fact]
  public async Task ImportFromRefinedModuleAndParseCaching() {

    var usingFile = @"
include ""./importFromRefinedModuleUsingField.dfy""

module A {
  import Refiner
  import Library

  method Bar() {
    var c := Library.True;
    var x := Refiner.Foo(c);
  }
}
";
    var testFiles = Path.Combine(Directory.GetCurrentDirectory(), "Synchronization/TestFiles");
    var documentItem1 = CreateTestDocument(usingFile, Path.Combine(testFiles, "test.dfy"));
    await client.OpenDocumentAndWaitAsync(documentItem1, CancellationToken);

    var documentItem2 = CreateTestDocument(usingFile, Path.Combine(testFiles, "test2.dfy"));
    await client.OpenDocumentAndWaitAsync(documentItem2, CancellationToken);
    await AssertNoDiagnosticsAreComing(CancellationToken);
  }

  [Fact]
  public async Task PotentialImportOpenedConflict() {
    var usingFile = @"
include ""./potentialImportOpenedConflict.dfy""


module ChangedClonedId {
    const changed := 2
}
";
    var testFiles = Path.Combine(Directory.GetCurrentDirectory(), "Synchronization/TestFiles");
    var documentItem1 = CreateTestDocument(usingFile, Path.Combine(testFiles, "notCached.dfy"));
    await client.OpenDocumentAndWaitAsync(documentItem1, CancellationToken);
    var diagnostics1 = await GetLastDiagnostics(documentItem1, CancellationToken);
    Assert.Empty(diagnostics1.Where(d => d.Severity == DiagnosticSeverity.Error));

    ApplyChange(ref documentItem1, new Range(2, 0, 2, 0), "//comment\n");
    await AssertNoDiagnosticsAreComing(CancellationToken);
  }

  public CachingTest(ITestOutputHelper output) : base(output) {
  }
}