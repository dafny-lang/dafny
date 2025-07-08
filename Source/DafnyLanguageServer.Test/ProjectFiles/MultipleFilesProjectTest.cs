using System;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;
using Xunit.Abstractions;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.ProjectFiles;

public class MultipleFilesProjectTest : ClientBasedLanguageServerTest {

  [Fact]
  public async Task OnDiskProducerResolutionErrors() {
    var producerSource = @"
method Foo(x: int) { 
  var y: char := 3.0;
}
".TrimStart();

    var consumerSource = @"
method Bar() {
  Foo(true); 
}
";

    var directory = GetFreshTempPath();
    Directory.CreateDirectory(directory);
    await File.WriteAllTextAsync(Path.Combine(directory, "producer.dfy"), producerSource);
    await File.WriteAllTextAsync(Path.Combine(directory, DafnyProject.FileName), "");
    await CreateOpenAndWaitForResolve(consumerSource, Path.Combine(directory, "src/consumer1.dfy"));

    var diagnostics1 = await diagnosticsReceiver.AwaitNextNotificationAsync(CancellationToken);
    var diagnostics2 = await diagnosticsReceiver.AwaitNextNotificationAsync(CancellationToken);
    var diagnostics3 = await diagnosticsReceiver.AwaitNextNotificationAsync(CancellationToken);
    var diagnostics = new[] { diagnostics1, diagnostics2, diagnostics3 };
    Assert.Single(diagnostics1.Diagnostics);
    Assert.Single(diagnostics2.Diagnostics);
    Assert.Contains(diagnostics, d => d.Diagnostics.First().Message.Contains("char"));
    Assert.Contains(diagnostics, d => d.Diagnostics.First().Message.Contains("int"));
    Directory.Delete(directory, true);
  }

  [Fact]
  public async Task OnDiskProducerVerificationErrorsChangeFile() {

    var producerSource = @"
method Foo(x: int) 
{
  assert false; 
}
".TrimStart();

    var consumerSource = @"
method Bar() {
  Foo(3); 
  assert false; 
}
";

    var directory = GetFreshTempPath();
    Directory.CreateDirectory(directory);
    await File.WriteAllTextAsync(Path.Combine(directory, "OnDiskProducerVerificationErrors_producer.dfy"), producerSource);
    await File.WriteAllTextAsync(Path.Combine(directory, DafnyProject.FileName), "");
    var consumer = await CreateOpenAndWaitForResolve(consumerSource, Path.Combine(directory, "OnDiskProducerVerificationErrors_consumer1.dfy"));

    var diagnostics1 = await GetLastDiagnostics(consumer);
    Assert.Single(diagnostics1);
    Assert.Contains("assertion might not hold", diagnostics1.First().Message);
    await AssertNoDiagnosticsAreComing(CancellationToken);
    Directory.Delete(directory, true);
  }

  [Fact]
  public async Task OnDiskProducerVerificationErrorsChangeProject() {
    await SetUp(options => options.Set(ProjectManager.Verification, VerifyOnMode.ChangeProject));

    var producerSource = @"
method Foo(x: int) 
{
  assert false; 
}
".TrimStart();

    var consumerSource = @"
method Bar() {
  Foo(3); 
  assert false; 
}
";

    var directory = GetFreshTempPath();
    Directory.CreateDirectory(directory);
    var producerPath = Path.Combine(directory, "OnDiskProducerVerificationErrors_producer.dfy");
    var producerUri = DocumentUri.File(producerPath);
    await File.WriteAllTextAsync(producerPath, producerSource);
    await File.WriteAllTextAsync(Path.Combine(directory, DafnyProject.FileName), "");
    var consumer = await CreateOpenAndWaitForResolve(consumerSource, Path.Combine(directory, "OnDiskProducerVerificationErrors_consumer1.dfy"));

    var producer = new TextDocumentItem() {
      Version = null,
      Uri = producerUri
    };
    var consumerDiagnostics = await GetLastDiagnostics(consumer);
    var producerDiagnostics = await GetLastDiagnostics(producer);

    Assert.Single(consumerDiagnostics);
    Assert.Contains("assertion might not hold", consumerDiagnostics.First().Message);
    Assert.Single(producerDiagnostics);
    Assert.Contains("assertion might not hold", producerDiagnostics.First().Message);
    Directory.Delete(directory, true);
  }

  [Fact]
  public async Task FileGetsRemappedToProjectByCreatingProjectFileOnDisk() {
    var consumerSource = @"
method Consumes() {
  Produces();
}
".TrimStart();

    var producer = @"
method Produces() {}
".TrimStart();

    var directory = GetFreshTempPath();
    Directory.CreateDirectory(directory);
    var consumer = await CreateOpenAndWaitForResolve(consumerSource, Path.Combine(directory, "firstFile.dfy"));
    await CreateOpenAndWaitForResolve(producer, Path.Combine(directory, "secondFile.dfy"));

    var producesDefinition1 = await RequestDefinition(consumer, new Position(1, 3));
    Assert.Empty(producesDefinition1);

    await File.WriteAllTextAsync(Path.Combine(directory, DafnyProject.FileName), "includes = [\"*.dfy\"]");

    var producesDefinition2 = await RequestDefinition(consumer, new Position(1, 3));
    Assert.Single(producesDefinition2);
    Directory.Delete(directory, true);
  }

  [Fact]
  public async Task FileGetsRemappedToProjectByOpeningUnsavedProjectFile() {
    var consumerSource = @"
method Consumes() {
  Produces();
}
".TrimStart();

    var producer = @"
method Produces() {}
".TrimStart();

    var directory = Path.GetRandomFileName();
    var consumer = await CreateOpenAndWaitForResolve(consumerSource, Path.Combine(directory, "firstFile.dfy"));
    var secondFile = await CreateOpenAndWaitForResolve(producer, Path.Combine(directory, "secondFile.dfy"));

    var producesDefinition1 = await RequestDefinition(consumer, new Position(1, 3));
    Assert.Empty(producesDefinition1);

    await CreateOpenAndWaitForResolve("", Path.Combine(directory, DafnyProject.FileName));

    var producesDefinition2 = await RequestDefinition(consumer, new Position(1, 3));
    Assert.Single(producesDefinition2);
  }

  [Fact]
  public async Task ClosingAllFilesInAProjectClosesTheProject() {
    await SetUp(options => {
      options.Set(BoogieOptionBag.Cores, 1U);
    });

    var directory = Path.GetRandomFileName();
    var projectFile = await CreateOpenAndWaitForResolve("", Path.Combine(directory, DafnyProject.FileName));
    var codeFile = await CreateOpenAndWaitForResolve("method Foo() {}", Path.Combine(directory, "firstFile.dfy"));

    Assert.NotEmpty(Projects.Managers);

    client.CloseDocument(projectFile);
    await client.WaitForNotificationCompletionAsync(codeFile.Uri, CancellationToken);
    Assert.NotEmpty(Projects.Managers);

    client.CloseDocument(codeFile);
    var retryCount = 10;
    for (int i = 0; i < retryCount; i++) {
      if (!Projects.Managers.Any()) {
        break;
      }
      await Task.Delay(100);
    }
  }

  [Fact]
  public async Task OnDiskChangesToProjectFileAffectCodeNavigation() {
    var projectFileSource = @"includes = [""firstFile.dfy""]";

    var consumerSource = @"
method Consumes() {
  Produces();
}
".TrimStart();

    var producer = @"
method Produces() {}
".TrimStart();

    var directory = GetFreshTempPath();
    Directory.CreateDirectory(directory);
    var projectFilePath = Path.Combine(directory, DafnyProject.FileName);
    await File.WriteAllTextAsync(projectFilePath, projectFileSource);

    var consumer = await CreateOpenAndWaitForResolve(consumerSource, Path.Combine(directory, "firstFile.dfy"));
    var secondFile = await CreateOpenAndWaitForResolve(producer, Path.Combine(directory, "secondFile.dfy"));

    var producesDefinition1 = await RequestDefinition(consumer, new Position(1, 3));
    Assert.Empty(producesDefinition1);

    await FileTestExtensions.WriteWhenUnlocked(projectFilePath, @"includes = [""firstFile.dfy"", ""secondFile.dfy""]");

    var producesDefinition2 = await RequestDefinition(consumer, new Position(1, 3));
    Assert.Single(producesDefinition2);
    Directory.Delete(directory, true);
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
".Trim(); // includes must come before [options], even if there is a blank line
    var directory = Path.GetRandomFileName();
    var projectFile = await CreateOpenAndWaitForResolve(projectFileSource, Path.Combine(directory, DafnyProject.FileName));
    var sourceFile = await CreateOpenAndWaitForResolve(source, Path.Combine(directory, "src/file.dfy"));

    var diagnostics1 = await GetLastDiagnostics(sourceFile);
    Assert.Equal(2, diagnostics1.Count(d => d.Severity <= DiagnosticSeverity.Warning));
    Assert.Contains(diagnostics1, s => s.Message.Contains("Shadowed"));

    ApplyChange(ref projectFile, new Range(3, 17, 3, 21), "false");

    var resolutionDiagnostics2 = await diagnosticsReceiver.AwaitNextWarningOrErrorDiagnosticsAsync(CancellationToken);
    // The shadowed warning is no longer produced, and the verification error is not migrated. 
    Assert.Empty(resolutionDiagnostics2);
  }

  [Fact]
  public async Task UpdateProducingFileWithExplicitProject() {
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
    var directory = Path.GetRandomFileName();
    var projectFile = await CreateOpenAndWaitForResolve(projectFileSource, Path.Combine(directory, DafnyProject.FileName));
    var producerItem = await CreateOpenAndWaitForResolve(producerSource, Path.Combine(directory, "src/producer.dfy"));
    var consumer = await CreateOpenAndWaitForResolve(consumerSource, Path.Combine(directory, "src/consumer1.dfy"));

    var consumerDiagnostics1 = await GetLastDiagnostics(consumer);
    Assert.Single(consumerDiagnostics1);
    Assert.Contains("int", consumerDiagnostics1[0].Message);

    ApplyChange(ref producerItem, new Range(0, 14, 0, 17), "bool");
    await WaitUntilAllStatusAreCompleted(producerItem);
    var consumerDiagnostics2 = await GetLastDiagnostics(consumer, allowStale: true);
    Assert.Empty(consumerDiagnostics2);
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
    var producerItem = await CreateOpenAndWaitForResolve(producerSource, Path.Combine(Directory.GetCurrentDirectory(), "A.dfy"));
    var consumer = await CreateOpenAndWaitForResolve(consumerSource, Path.Combine(Directory.GetCurrentDirectory(), "consumer1.dfy"));

    var consumer1Diagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken, consumer);
    Assert.Single(consumer1Diagnostics);
    Assert.Contains("int", consumer1Diagnostics[0].Message);

    ApplyChange(ref producerItem, new Range(0, 0, 2, 0), "");

    var consumer2 = await CreateOpenAndWaitForResolve(consumerSource, Path.Combine(Directory.GetCurrentDirectory(), "consumer2.dfy"));
    var consumer2Diagnostics = await GetLastDiagnostics(consumer2);
    Assert.True(consumer2Diagnostics.Length > 1);

    client.CloseDocument(producerItem);
    var consumer3 = await CreateOpenAndWaitForResolve(consumerSource, Path.Combine(Directory.GetCurrentDirectory(), "consumer3.dfy"));
    var consumer3Diagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken, consumer3);
    Assert.Single(consumer3Diagnostics);
    Assert.Contains("not found", consumer3Diagnostics[0].Message);
  }

  public MultipleFilesProjectTest(ITestOutputHelper output) : base(output, LogLevel.Trace) {
  }
}