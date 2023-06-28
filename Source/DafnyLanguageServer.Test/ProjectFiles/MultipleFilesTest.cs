using System.IO;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.ProjectFiles; 

public class MultipleFilesTest : ClientBasedLanguageServerTest {

  [Fact]
  public async Task OpenUpdateCloseIncludedFileWithExplicitProject() {
    var producerSource = @"
method Foo(x: int) { 
}
".TrimStart();

    var consumerSource = @"
method Bar() {
  Foo(true); 
}
";

    var projectFileSource = @"
includes = [""src/**/*.dfy""]
";
    var directory = Directory.GetCurrentDirectory();
    var projectFile = CreateTestDocument(projectFileSource, Path.Combine(directory, "dfyconfig.toml"));
    await client.OpenDocumentAndWaitAsync(projectFile, CancellationToken);
    var producerItem = CreateTestDocument(producerSource, Path.Combine(directory, "src/producer.dfy"));
    await client.OpenDocumentAndWaitAsync(producerItem, CancellationToken);
    var consumer = CreateTestDocument(consumerSource, Path.Combine(directory, "src/consumer1.dfy"));
    await client.OpenDocumentAndWaitAsync(consumer, CancellationToken);

    var consumerDiagnostics1 = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken, consumer);
    Assert.Single(consumerDiagnostics1);
    Assert.Contains("int", consumerDiagnostics1[0].Message);

    ApplyChange(ref producerItem, new Range(0, 14, 0, 17), "bool");
    var consumerDiagnostics2 = await diagnosticsReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.Equal(consumer.Uri, consumerDiagnostics2.Uri);
    Assert.Empty(consumerDiagnostics2.Diagnostics);
  }

  [Fact]
  public async Task OpenUpdateCloseIncludedFileWithImplicitProject() {
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
    var consumer = CreateTestDocument(consumerSource, Path.Combine(Directory.GetCurrentDirectory(), "consumer1.dfy"));
    await client.OpenDocumentAndWaitAsync(consumer, CancellationToken);

    var consumer1Diagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken, consumer);
    Assert.Single(consumer1Diagnostics);
    Assert.Contains("int", consumer1Diagnostics[0].Message);

    ApplyChange(ref producerItem, new Range(0, 0, 2, 0), "");
    var producerDiagnostics2 = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken, producerItem);
    Assert.Single(producerDiagnostics2); // File has no code

    var consumer2 = CreateTestDocument(consumerSource, Path.Combine(Directory.GetCurrentDirectory(), "consumer2.dfy"));
    await client.OpenDocumentAndWaitAsync(consumer2, CancellationToken);
    var consumer2Diagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken, consumer2);
    Assert.True(consumer2Diagnostics.Length > 1);

    await client.CloseDocumentAndWaitAsync(producerItem, CancellationToken);
    var producerDiagnostics3 = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.Empty(producerDiagnostics3); // File has no code
    var consumer3 = CreateTestDocument(consumerSource, Path.Combine(Directory.GetCurrentDirectory(), "consumer3.dfy"));
    await client.OpenDocumentAndWaitAsync(consumer3, CancellationToken);
    var consumer3Diagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken, consumer3);
    Assert.Single(consumer3Diagnostics);
    Assert.Contains("Unable to open", consumer3Diagnostics[0].Message);
  }

  public MultipleFilesTest(ITestOutputHelper output) : base(output) {
  }
}