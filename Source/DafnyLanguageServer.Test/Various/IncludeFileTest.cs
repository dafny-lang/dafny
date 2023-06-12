using System;
using System.IO;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various;

public class IncludeFileTest : ClientBasedLanguageServerTest {

  [Fact]
  public async Task DirectlyIncludedFileFails() {
    var source = @"
include ""./syntaxError.dfy""
".TrimStart();
    var documentItem = CreateTestDocument(source, Path.Combine(Directory.GetCurrentDirectory(), "Synchronization/TestFiles/test.dfy"));
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var diagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.Single(diagnostics);
    Assert.Contains("the included file", diagnostics[0].Message);
    Assert.Contains("syntaxError.dfy", diagnostics[0].Message);
  }

  [Fact]
  public async Task IndirectlyIncludedFileFails() {
    var source = @"
include ""./includesSyntaxError.dfy""
".TrimStart();
    var documentItem = CreateTestDocument(source, Path.Combine(Directory.GetCurrentDirectory(), "Synchronization/TestFiles/test.dfy"));
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var diagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.Single(diagnostics);
    Assert.Contains("the included file", diagnostics[0].Message);
    Assert.Contains("syntaxError.dfy", diagnostics[0].Message);
  }

  [Fact]
  public async Task MutuallyRecursiveIncludes() {
    string rootFile = Path.Combine(Directory.GetCurrentDirectory(), "Various", "TestFiles", "includesBincludesA.dfy");
    var documentItem2 = CreateTestDocument(await File.ReadAllTextAsync(rootFile), rootFile);
    client.OpenDocument(documentItem2);
    var verificationDiagnostics = await GetLastDiagnostics(documentItem2, CancellationToken);
    Assert.Empty(verificationDiagnostics);
  }

  [Fact]
  public async Task MethodWhosePostConditionFailsAndDependsOnIncludedFile() {
    var temp = (Path.GetTempFileName() + ".dfy").Replace("\\", "/");
    var producer = @"
function Foo(x: int): bool {
  x == 2
}".TrimStart();
    var consumer = $@"
include ""{temp}""

method Bar(x: int) 
ensures Foo(x) {{

}}".TrimStart();
    await File.WriteAllTextAsync(temp, producer);
    var documentItem2 = CreateTestDocument(consumer);
    client.OpenDocument(documentItem2);
    var verificationDiagnostics = await GetLastDiagnostics(documentItem2, CancellationToken);
    Assert.Single(verificationDiagnostics);
    await AssertNoDiagnosticsAreComing(CancellationToken);
  }

  public IncludeFileTest(ITestOutputHelper output) : base(output) {
  }
}
