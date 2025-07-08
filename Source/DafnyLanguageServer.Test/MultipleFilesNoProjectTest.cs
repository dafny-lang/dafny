using System.IO;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest;

public class MultipleFilesNoProjectTest : ClientBasedLanguageServerTest {
  [Fact]
  public async Task OpenUpdateCloseIncludedFile() {
    var producerSource = @"
method Foo() { 
}
".TrimStart();

    var consumerSource = @"
include ""./A.dfy""
method Bar() {
  Foo();
  var x: int := true; 
}
";
    var producerItem = CreateTestDocument(producerSource, Path.Combine(Directory.GetCurrentDirectory(), "A.dfy"));
    await client.OpenDocumentAndWaitAsync(producerItem, CancellationToken);
    var consumer1 = CreateTestDocument(consumerSource, Path.Combine(Directory.GetCurrentDirectory(), "consumer1.dfy"));
    await client.OpenDocumentAndWaitAsync(consumer1, CancellationToken);

    var consumer1Diagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken, consumer1);
    Assert.Single(consumer1Diagnostics);
    Assert.Contains("int", consumer1Diagnostics[0].Message);

    ApplyChange(ref producerItem, new Range(0, 0, 2, 0), "");

    var consumer2 = CreateTestDocument(consumerSource, Path.Combine(Directory.GetCurrentDirectory(), "consumer2.dfy"));
    await client.OpenDocumentAndWaitAsync(consumer2, CancellationToken);
    var consumer2Diagnostics = await GetLastDiagnostics(consumer2);
    Assert.True(consumer2Diagnostics.Length > 1);

    client.CloseDocument(producerItem);
    var consumer3 = CreateTestDocument(consumerSource, Path.Combine(Directory.GetCurrentDirectory(), "consumer3.dfy"));
    await client.OpenDocumentAndWaitAsync(consumer3, CancellationToken);
    var consumer3Diagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken, consumer3);
    Assert.Single(consumer3Diagnostics);
    Assert.Contains("not found", consumer3Diagnostics[0].Message);
  }

  public MultipleFilesNoProjectTest(ITestOutputHelper output) : base(output) {
  }
}