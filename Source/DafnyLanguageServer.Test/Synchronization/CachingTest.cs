using System.IO;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.DependencyInjection.Extensions;
using Microsoft.Extensions.Logging;
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
  public async Task ParsingIsCachedAndCacheIsPruned() {
    var source = @"
include ""./A.dfy""
include ""./B.dfy""
module ModC {
  lemma Lem() ensures false {}
}
".TrimStart();
    var documentItem = CreateTestDocument(source, Path.Combine(Directory.GetCurrentDirectory(), "Synchronization/TestFiles/test.dfy"));
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var hits0 = await WaitAndCountHits();
    Assert.Equal(0, hits0);

    async Task<int> WaitAndCountHits() {
      await client.WaitForNotificationCompletionAsync(documentItem.Uri, CancellationToken);
      return sink.Snapshot().LogEvents.Count(le => le.MessageTemplate.Text.Contains("Parse cache hit"));
    }

    ApplyChange(ref documentItem, ((0, 0), (0, 0)), "// Pointless comment that triggers a reparse\n");
    var hitCount1 = await WaitAndCountHits();
    Assert.Equal(2, hitCount1);

    // Removes the comment and the include of B.dfy, which will prune the cache for B.dfy
    ApplyChange(ref documentItem, ((2, 0), (3, 0)), "");
    var hitCount2 = await WaitAndCountHits();
    Assert.Equal(hitCount1 + 1, hitCount2);

    ApplyChange(ref documentItem, ((0, 0), (0, 0)), @"include ""./B.dfy""\n");
    var hitCount3 = await WaitAndCountHits();
    // No hit for B.dfy, since it was previously pruned
    Assert.Equal(hitCount2 + 1, hitCount3);
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
    Assert.Equal(0, await WaitAndCountHits());

    ApplyChange(ref secondFile, ((0, 0), (0, 0)), "// Make the file larger\n");
    Assert.Equal(0, await WaitAndCountHits());

    // Removes the comment and the include of B.dfy, which will prune the cache for B.dfy
    ApplyChange(ref secondFile, ((19, 0), (19, 0)), "// Make the file larger\n");
    Assert.Equal(0, await WaitAndCountHits());
  }

  public CachingTest(ITestOutputHelper output) : base(output) {
  }
}