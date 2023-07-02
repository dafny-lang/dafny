using System;
using System.Collections;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Workspace;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;
using Xunit.Abstractions;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.ProjectFiles; 

public class MultipleFilesTest : ClientBasedLanguageServerTest {

  [Fact]
  public async Task FileGetsRemappedToProjectByCreatingProjectFile() {
    var consumerSource = @"
method Consumes() {
  Produces();
}
".TrimStart();

    var producer = @"
method Produces() {}
".TrimStart();

    var directory = Path.GetRandomFileName();
    var consumer = CreateTestDocument(consumerSource, Path.Combine(directory, "firstFile.dfy"));
    await client.OpenDocumentAndWaitAsync(consumer, CancellationToken);
    var secondFile = CreateTestDocument(producer, Path.Combine(directory, "secondFile.dfy"));
    await client.OpenDocumentAndWaitAsync(secondFile, CancellationToken);

    var producesDefinition1 = await RequestDefinition(consumer, new Position(1, 3));
    Assert.Empty(producesDefinition1);

    var projectFile = CreateTestDocument("", Path.Combine(directory, "dfyconfig.toml"));
    await client.OpenDocumentAndWaitAsync(projectFile, CancellationToken);

    var producesDefinition2 = await RequestDefinition(consumer, new Position(1, 3));
    Assert.Single(producesDefinition2);
  }

  [Fact]
  public async Task ClosingAllFilesInAProjectClosesTheProject() {
    await SetUp(options => {
      options.Set(BoogieOptionBag.Cores, 1U);
    });

    var directory = Path.GetRandomFileName();
    var projectFile = CreateTestDocument("", Path.Combine(directory, "dfyconfig.toml"));
    await client.OpenDocumentAndWaitAsync(projectFile, CancellationToken);
    var codeFile = CreateTestDocument("method Foo() {}", Path.Combine(directory, "firstFile.dfy"));
    await client.OpenDocumentAndWaitAsync(codeFile, CancellationToken);

    Assert.NotEmpty(Projects.Managers);

    await client.CloseDocumentAndWaitAsync(projectFile, CancellationToken);
    Assert.NotEmpty(Projects.Managers);

    await client.CloseDocumentAndWaitAsync(codeFile, CancellationToken);

    var retryCount = 10;
    for (int i = 0; i < retryCount; i++) {
      if (!Projects.Managers.Any()) {
        break;
      }
      await Task.Delay(100);
    }
  }

  [Fact]
  public async Task VerificationPriorityBasedOnChangesWorksWithMultipleFiles() {
    await SetUp(options => {
      options.Set(BoogieOptionBag.Cores, 1U);
    });

    var sourceA = @"
method Foo() {
  assert false;
}
".TrimStart();

    var sourceB = @"
method Bar() {
  assert false;
}
".TrimStart();

    var directory = Path.GetRandomFileName();
    var projectFile = CreateTestDocument("", Path.Combine(directory, "dfyconfig.toml"));
    await client.OpenDocumentAndWaitAsync(projectFile, CancellationToken);
    var firstFile = CreateTestDocument(sourceA, Path.Combine(directory, "firstFile.dfy"));
    await client.OpenDocumentAndWaitAsync(firstFile, CancellationToken);
    var secondFile = CreateTestDocument(sourceB, Path.Combine(directory, "secondFile.dfy"));
    await client.OpenDocumentAndWaitAsync(secondFile, CancellationToken);

    var history0 = await WaitUntilCompletedForUris(2, CancellationToken);

    ApplyChange(ref secondFile, new Range(1, 0, 1, 0), "  //comment before assert false\n");

    var history1 = await WaitUntilCompletedForUris(2, CancellationToken);
    Assert.Equal(firstFile.Uri.ToUri(), history1[^1].Uri);
    ApplyChange(ref firstFile, new Range(1, 0, 1, 0), "  //comment before assert false\n");

    var history2 = await WaitUntilCompletedForUris(2, CancellationToken);
    Assert.Equal(secondFile.Uri.ToUri(), history2[^1].Uri);
  }

  [Fact]
  public async Task ExplicitProjectToGoDefinitionWorks() {
    var sourceA = @"
const a := 3;
const b := a + 2;
".TrimStart();

    var directory = Path.GetRandomFileName();
    var projectFile = CreateTestDocument("", Path.Combine(directory, "dfyconfig.toml"));
    await client.OpenDocumentAndWaitAsync(projectFile, CancellationToken);
    var firstFile = CreateTestDocument(sourceA, Path.Combine(directory, "firstFile.dfy"));
    await client.OpenDocumentAndWaitAsync(firstFile, CancellationToken);

    var result1 = await RequestDefinition(firstFile, new Position(1, 11));
    Assert.Equal(new Range(0, 6, 0, 7), result1.Single().Location!.Range);
  }

  [Fact]
  public async Task ChangesToProjectFileAffectDiagnosticsAndLoseMigration() {
    var source = @"
method Bar(shadowed: int) {
  var i := shadowed;
  while(i > 0) {
    var shadowed := 1;
    i := i - shadowed;
  }
}

method Foo() {
  assert false;
}
";

    var projectFileSource = @"
includes = [""src/**/*.dfy""]

[options]
warn-shadowing = true
"; // includes must come before [options], even if there is a blank line
    var directory = Path.GetRandomFileName();
    var projectFile = CreateTestDocument(projectFileSource, Path.Combine(directory, "dfyconfig.toml"));
    await client.OpenDocumentAndWaitAsync(projectFile, CancellationToken);
    var sourceFile = CreateTestDocument(source, Path.Combine(directory, "src/file.dfy"));
    await client.OpenDocumentAndWaitAsync(sourceFile, CancellationToken);

    var diagnostics1 = await GetLastDiagnostics(sourceFile, CancellationToken);
    Assert.Equal(2, diagnostics1.Length);
    Assert.Contains("Shadowed", diagnostics1[0].Message);

    ApplyChange(ref projectFile, new Range(1, 17, 1, 21), "false");

    var resolutionDiagnostics2 = await diagnosticsReceiver.AwaitNextWarningOrErrorDiagnosticsAsync(CancellationToken);
    // The shadowed warning is no longer produced, and the verification error is not migrated. 
    Assert.Empty(resolutionDiagnostics2);
  }

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