using System;
using System.IO;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various;

public class IncludeFileTest : ClientBasedLanguageServerTest {
  private static readonly string TestFileDirectory = Path.Combine(Directory.GetCurrentDirectory(), "Synchronization", "TestFiles");
  private static readonly string TestFilePath = Path.Combine(TestFileDirectory, "testFile.dfy");

  // https://github.com/dafny-lang/language-server-csharp/issues/40
  [Fact]
  public async Task ImplicitlyIncludingTheSameModuleTwiceDoesNotResultInDuplicateError() {
    var source = @"
include ""multi1.dfy""
include ""multi2.dfy""

method Test() {
  assert true;
}";
    var documentItem = CreateTestDocument(source, TestFilePath);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var document = await Projects.GetResolvedDocumentAsyncNormalizeUri(documentItem.Uri);
    Assert.NotNull(document);
    Assert.Empty(document.GetAllDiagnostics());
  }

  // https://github.com/dafny-lang/language-server-csharp/issues/40
  [Fact]
  public async Task ImplicitlyIncludingTheSameModuleTwiceDoesNotOverrideActualError() {
    var source = @"
include ""multi1.dfy""
include ""multi2.dfy""

method Test() {
  assert false;
}";
    var documentItem = CreateTestDocument(source, TestFilePath);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var document = await Projects.GetLastDocumentAsync(documentItem.Uri);
    Assert.NotNull(document);
    Assert.Single(document.GetDiagnostics(documentItem.Uri.ToUri()));
  }

  [Fact]
  public async Task NonErrorDiagnosticDoesNotProduceAnError() {
    var source = @"
include ""./hasWarning.dfy""
".TrimStart();
    var warningSource = "const tooManySemiColons := 3;";
    await CreateOpenAndWaitForResolve(warningSource, Path.Combine(TestFileDirectory, "hasWarning.dfy"));
    await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    await CreateOpenAndWaitForResolve(source, TestFilePath);
    await AssertNoDiagnosticsAreComing(CancellationToken);
  }

  [Fact]
  public async Task DirectlyIncludedFileFails() {
    var source = @"
include ""./syntaxError.dfy""
".TrimStart();
    var documentItem = CreateTestDocument(source, TestFilePath);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var diagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.Single(diagnostics);
    Assert.Contains("the referenced file", diagnostics[0].Message);
    Assert.Contains("syntaxError.dfy", diagnostics[0].Message);
  }

  [Fact]
  public async Task IndirectlyIncludedFileFailsSyntax() {
    var source = @"
include ""./includesSyntaxError.dfy""
include ""./syntaxError.dfy""
".TrimStart();
    var documentItem = CreateTestDocument(source, TestFilePath);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var diagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.Single(diagnostics);
    Assert.Contains("the referenced file", diagnostics[0].Message);
    Assert.Contains("The first error is:\nrbrace expected", diagnostics[0].Message);
    Assert.Contains("syntaxError.dfy", diagnostics[0].Message);
  }

  [Fact]
  public async Task IncludeCycle() {
    var source = @"
include ""./cycleA.dfy""
".TrimStart();
    var documentItem = CreateTestDocument(source, TestFilePath);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    // Parse diagnostics are currently only sent if they contain errors
    // var parseDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    // Assert.Single(parseDiagnostics);
    // Assert.Contains(parseDiagnostics, d => d.Message.Contains("cycle of includes"));
    var resolutionDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.Equal(2, resolutionDiagnostics.Length);
    Assert.Contains(resolutionDiagnostics, d => d.Message.Contains("cycle of includes"));
    Assert.Contains(resolutionDiagnostics, d => d.Message.Contains("the referenced file"));
    Assert.Contains(resolutionDiagnostics, d => d.Message.Contains("the referenced file") && d.Message.Contains("cycleB.dfy"));
  }

  [Fact]
  public async Task IndirectlyIncludedFileFailsSemantic() {
    var source = @"
include ""./includesSemanticError.dfy""
include ""./semanticError.dfy""
".TrimStart();
    var documentItem = CreateTestDocument(source, TestFilePath);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var diagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.Single(diagnostics);
    Assert.Contains("the referenced file", diagnostics[0].Message);
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
    var documentItem2 = CreateTestDocument(consumer, "MethodWhosePostConditionFailsAndDependsOnIncludedFile.dfy");
    client.OpenDocument(documentItem2);
    var verificationDiagnostics = await GetLastDiagnostics(documentItem2, CancellationToken);
    Assert.Single(verificationDiagnostics);
    await AssertNoDiagnosticsAreComing(CancellationToken);
  }

  public IncludeFileTest(ITestOutputHelper output) : base(output) {
  }
}
