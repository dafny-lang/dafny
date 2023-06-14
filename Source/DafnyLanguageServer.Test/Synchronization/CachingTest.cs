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
  public async Task RootFileChangesTriggerParseAndResolutionCachingAndPruning() {
    var source = @"
include ""./A.dfy""
include ""./B.dfy""
module ModC {
  import ModB
  import ModA
  const z := ModB.y + 1
  lemma Lem() ensures false {}

  const usage := ModB.calledModAFunction
  const calledModAFunction := ModA.TakesIdentityAndAppliesIt((x, _) => x, 3)
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
    var diagnostics = await GetLastDiagnostics(documentItem, CancellationToken);
    Assert.Empty(diagnostics.Where(d => d.Severity == DiagnosticSeverity.Error));
    Assert.Equal(2, hitCount1.ParseHits);
    // literal A, alias A (in Literal B), and literal B. Alias B's CloneId is tainted because it resides in the changed file. 
    Assert.Equal(3, hitCount1.ResolveHits);

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
    // The resolution cache was pruned after the previous change, so no cache hits here.
    Assert.Equal(hitCount2.ResolveHits, hitCount3.ResolveHits);
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

  public CachingTest(ITestOutputHelper output) : base(output) {
  }
}