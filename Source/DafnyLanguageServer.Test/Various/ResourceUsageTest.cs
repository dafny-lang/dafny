using System.Diagnostics;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various;

[Collection("Sequential Collection")] // Because this a performance test, we can't run in in parallel with others
public class ResourceUsageTest : ClientBasedLanguageServerTest {

  [Fact]
  public async Task SolverProcessCountDoesNotIncreaseOnEachVerification() {
    var source = @"
method Foo()
{
    assert false;
}";
    string solverProcessName = $"z3-{DafnyOptions.DefaultZ3Version}";
    var processes1 = Process.GetProcessesByName(solverProcessName);
    var documentItem = CreateTestDocument(source, "SolverProcessCountDoesNotIncreaseOnEachVerification.dfy");
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

    await GetLastDiagnostics(documentItem);
    var processes2 = Process.GetProcessesByName(solverProcessName);
    Assert.Equal(processes1.Length, processes2.Length - 1);
    ApplyChange(ref documentItem, new Range(0, 0, 0, 0), "\n");
    await GetLastDiagnostics(documentItem);
    var processes3 = Process.GetProcessesByName(solverProcessName);
    Assert.Equal(processes2.Length, processes3.Length);
  }

  public ResourceUsageTest(ITestOutputHelper output) : base(output) {
  }
}
