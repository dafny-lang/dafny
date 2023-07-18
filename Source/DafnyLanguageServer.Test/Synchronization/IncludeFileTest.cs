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
  public async Task IndirectlyIncludedFileFailsSyntax() {
    var source = @"
include ""./includesSyntaxError.dfy""
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
  public async Task IncludeCycle() {
    var source = @"
include ""./cycleA.dfy""
".TrimStart();
    var documentItem = CreateTestDocument(source, Path.Combine(Directory.GetCurrentDirectory(), "Synchronization/TestFiles/test.dfy"));
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var diagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.Equal(2, diagnostics.Length);
    Assert.Contains("cycle of includes", diagnostics[0].Message);
    Assert.Contains("the included file", diagnostics[1].Message);
    Assert.Contains("cycleB.dfy", diagnostics[1].Message);
  }

  [Fact]
  public async Task IndirectlyIncludedFileFailsSemantic() {
    var source = @"
include ""./includesSemanticError.dfy""
include ""./semanticError.dfy""
".TrimStart();
    var documentItem = CreateTestDocument(source, Path.Combine(Directory.GetCurrentDirectory(), "Synchronization/TestFiles/test.dfy"));
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var diagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.Single(diagnostics);
    Assert.Contains("the included file", diagnostics[0].Message);
    Assert.Contains("semanticError.dfy", diagnostics[0].Message);
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
