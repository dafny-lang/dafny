using System;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Workspace;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Serilog.Core;
using Xunit;
using Xunit.Abstractions;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.ProjectFiles;

public class MultipleFilesTest : ClientBasedLanguageServerTest {
  protected override Task SetUp(Action<DafnyOptions> modifyOptions) {
    return base.SetUp(o => {
      o.Set(ServerCommand.ProjectMode, true);
      modifyOptions?.Invoke(o);
    });
  }

  [Fact]
  public async Task NoProjectModeWithProjectFileAndMultipleFiles() {
    await SetUp(o => {
      o.Set(ServerCommand.ProjectMode, false);
    });
    var producerSource = @"
method Foo(x: int) { 
  var y: char := 3.0;
}
".TrimStart();

    var consumerSource = @"
include ""A.dfy""
method Bar() {
  Foo(true); 
}
";

    var directory = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName());
    Directory.CreateDirectory(directory);
    await File.WriteAllTextAsync(Path.Combine(directory, DafnyProject.FileName), "");
    // The names A and B are important, because A must be alphabetically before B to trigger a particular cache without cloning bug 
    await File.WriteAllTextAsync(Path.Combine(directory, "A.dfy"), producerSource);
    await CreateAndOpenTestDocument(consumerSource, Path.Combine(directory, "B.dfy"));

    var consumerDiagnostics = await diagnosticsReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.Equal(2, consumerDiagnostics.Diagnostics.Count());
    Assert.Contains(consumerDiagnostics.Diagnostics, diagnostic => diagnostic.Message.Contains("bool"));
    await AssertNoDiagnosticsAreComing(CancellationToken);
  }

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

    var directory = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName());
    Directory.CreateDirectory(directory);
    await File.WriteAllTextAsync(Path.Combine(directory, "producer.dfy"), producerSource);
    await File.WriteAllTextAsync(Path.Combine(directory, DafnyProject.FileName), "");
    await CreateAndOpenTestDocument(consumerSource, Path.Combine(directory, "src/consumer1.dfy"));

    var diagnostics1 = await diagnosticsReceiver.AwaitNextNotificationAsync(CancellationToken);
    var diagnostics2 = await diagnosticsReceiver.AwaitNextNotificationAsync(CancellationToken);
    var diagnostics = new[] { diagnostics1, diagnostics2 };
    Assert.Single(diagnostics1.Diagnostics);
    Assert.Single(diagnostics2.Diagnostics);
    Assert.Contains(diagnostics, d => d.Diagnostics.First().Message.Contains("char"));
    Assert.Contains(diagnostics, d => d.Diagnostics.First().Message.Contains("int"));
  }

  [Fact]
  public async Task OnDiskProducerVerificationErrors() {
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

    var directory = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName());
    Directory.CreateDirectory(directory);
    await File.WriteAllTextAsync(Path.Combine(directory, "OnDiskProducerVerificationErrors_producer.dfy"), producerSource);
    await File.WriteAllTextAsync(Path.Combine(directory, DafnyProject.FileName), "");
    await CreateAndOpenTestDocument(consumerSource, Path.Combine(directory, "OnDiskProducerVerificationErrors_consumer1.dfy"));

    var diagnostics1 = await diagnosticsReceiver.AwaitNextNotificationAsync(CancellationToken);
    var diagnostics2 = await diagnosticsReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.Single(diagnostics1.Diagnostics);
    Assert.Contains("assertion might not hold", diagnostics1.Diagnostics.First().Message);
    Assert.Single(diagnostics2.Diagnostics);
    Assert.Contains("assertion might not hold", diagnostics2.Diagnostics.First().Message);
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

    var directory = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName());
    Directory.CreateDirectory(directory);
    var consumer = await CreateAndOpenTestDocument(consumerSource, Path.Combine(directory, "firstFile.dfy"));
    await CreateAndOpenTestDocument(producer, Path.Combine(directory, "secondFile.dfy"));

    var producesDefinition1 = await RequestDefinition(consumer, new Position(1, 3));
    Assert.Empty(producesDefinition1);

    await File.WriteAllTextAsync(Path.Combine(directory, DafnyProject.FileName), "includes = [\"*.dfy\"]");
    await Task.Delay(ProjectManagerDatabase.ProjectFileCacheExpiryTime);

    var producesDefinition2 = await RequestDefinition(consumer, new Position(1, 3));
    Assert.Single(producesDefinition2);
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
    var consumer = await CreateAndOpenTestDocument(consumerSource, Path.Combine(directory, "firstFile.dfy"));
    var secondFile = await CreateAndOpenTestDocument(producer, Path.Combine(directory, "secondFile.dfy"));

    var producesDefinition1 = await RequestDefinition(consumer, new Position(1, 3));
    Assert.Empty(producesDefinition1);

    await CreateAndOpenTestDocument("", Path.Combine(directory, DafnyProject.FileName));

    await Task.Delay(ProjectManagerDatabase.ProjectFileCacheExpiryTime);

    var producesDefinition2 = await RequestDefinition(consumer, new Position(1, 3));
    Assert.Single(producesDefinition2);
  }

  [Fact]
  public async Task ClosingAllFilesInAProjectClosesTheProject() {
    await SetUp(options => {
      options.Set(BoogieOptionBag.Cores, 1U);
    });

    var directory = Path.GetRandomFileName();
    var projectFile = await CreateAndOpenTestDocument("", Path.Combine(directory, DafnyProject.FileName));
    var codeFile = await CreateAndOpenTestDocument("method Foo() {}", Path.Combine(directory, "firstFile.dfy"));

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

    var directory = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName());
    Directory.CreateDirectory(directory);
    var projectFilePath = Path.Combine(directory, DafnyProject.FileName);
    await File.WriteAllTextAsync(projectFilePath, projectFileSource);

    var consumer = await CreateAndOpenTestDocument(consumerSource, Path.Combine(directory, "firstFile.dfy"));
    var secondFile = await CreateAndOpenTestDocument(producer, Path.Combine(directory, "secondFile.dfy"));

    var producesDefinition1 = await RequestDefinition(consumer, new Position(1, 3));
    Assert.Empty(producesDefinition1);

    await FileTestExtensions.WriteWhenUnlocked(projectFilePath, @"includes = [""firstFile.dfy"", ""secondFile.dfy""]");
    await Task.Delay(ProjectManagerDatabase.ProjectFileCacheExpiryTime);

    var producesDefinition2 = await RequestDefinition(consumer, new Position(1, 3));
    Assert.Single(producesDefinition2);
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
    var projectFile = await CreateAndOpenTestDocument(projectFileSource, Path.Combine(directory, DafnyProject.FileName));
    var sourceFile = await CreateAndOpenTestDocument(source, Path.Combine(directory, "src/file.dfy"));

    var diagnostics1 = await GetLastDiagnostics(sourceFile, CancellationToken);
    Assert.Equal(2, diagnostics1.Count(d => d.Severity <= DiagnosticSeverity.Warning));
    Assert.Contains(diagnostics1, s => s.Message.Contains("Shadowed"));

    await Task.Delay(ProjectManagerDatabase.ProjectFileCacheExpiryTime);
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
    var projectFile = await CreateAndOpenTestDocument(projectFileSource, Path.Combine(directory, DafnyProject.FileName));
    var producerItem = await CreateAndOpenTestDocument(producerSource, Path.Combine(directory, "src/producer.dfy"));
    var consumer = await CreateAndOpenTestDocument(consumerSource, Path.Combine(directory, "src/consumer1.dfy"));

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
    var producerItem = await CreateAndOpenTestDocument(producerSource, Path.Combine(Directory.GetCurrentDirectory(), "A.dfy"));
    var consumer = await CreateAndOpenTestDocument(consumerSource, Path.Combine(Directory.GetCurrentDirectory(), "consumer1.dfy"));

    var consumer1Diagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken, consumer);
    Assert.Single(consumer1Diagnostics);
    Assert.Contains("int", consumer1Diagnostics[0].Message);

    ApplyChange(ref producerItem, new Range(0, 0, 2, 0), "");
    var producerDiagnostics2 = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken, producerItem);
    Assert.Single(producerDiagnostics2); // File has no code

    var consumer2 = await CreateAndOpenTestDocument(consumerSource, Path.Combine(Directory.GetCurrentDirectory(), "consumer2.dfy"));
    var consumer2Diagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken, consumer2);
    Assert.True(consumer2Diagnostics.Length > 1);

    client.CloseDocument(producerItem);
    var producerDiagnostics3 = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.Empty(producerDiagnostics3); // File has no code
    var consumer3 = await CreateAndOpenTestDocument(consumerSource, Path.Combine(Directory.GetCurrentDirectory(), "consumer3.dfy"));
    var consumer3Diagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken, consumer3);
    Assert.Single(consumer3Diagnostics);
    Assert.Contains("Unable to open", consumer3Diagnostics[0].Message);
  }

  public MultipleFilesTest(ITestOutputHelper output) : base(output) {
  }
}