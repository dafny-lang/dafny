using System.IO;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Performance; 

public class LargeFiles : ClientBasedLanguageServerTest {

  [Fact]
  public async Task SlowEditsUsingLargeFilesAndIncludes() {
    var source = @"
include ""./veryLargeAndIncludesAnotherLarge.dfy""
";
    var documentItem = CreateTestDocument(source, Path.Combine(Directory.GetCurrentDirectory(), "Performance/TestFiles/test.dfy"));
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var diagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.Empty(diagnostics);
    for (int i = 0; i < 20; i++) {
      await Task.Delay(200);
      ApplyChange(ref documentItem, new Range(0, 0, 0, 0), "// added this comment\n");
    }
    await client.WaitForNotificationCompletionAsync(documentItem.Uri, CancellationToken);
    await AssertNoDiagnosticsAreComing(CancellationToken);
  }

  [Fact]
  public async Task ManyFastEditsUsingLargeFilesAndIncludes() {
    var source = @"
include ""./veryLargeAndIncludesAnotherLarge.dfy""
";
    var documentItem = CreateTestDocument(source, Path.Combine(Directory.GetCurrentDirectory(), "Performance/TestFiles/test.dfy"));
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var diagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.Empty(diagnostics);
    for (int i = 0; i < 300; i++) {
      ApplyChange(ref documentItem, new Range(0, 0, 0, 0), "// added this comment\n");
    }

    await client.WaitForNotificationCompletionAsync(documentItem.Uri, CancellationToken);
    await AssertNoDiagnosticsAreComing(CancellationToken);
  }

  public LargeFiles(ITestOutputHelper output) : base(output) {
  }
}