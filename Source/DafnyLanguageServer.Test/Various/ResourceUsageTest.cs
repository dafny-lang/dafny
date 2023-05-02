using System.Diagnostics;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various;

[Collection("Sequential Collection")] // Because this a performance test, we can't run in in parallel with others
public class ResourceUsageTest : ClientBasedLanguageServerTest {

  private int GetCurrentZ3Processes() {
    string solverProcessName = $"z3-{DafnyOptions.DefaultZ3Version}";
    var processes = Process.GetProcessesByName(solverProcessName);
    if (processes.Length == 0) {
      processes = Process.GetProcessesByName("z3");
      return processes.Length;
    } else {
      return processes.Length;
    }
  }

  [Fact]
  public async Task SolverProcessCountDoesNotIncreaseOnEachVerification() {
    var source = @"
method Foo()
{
    assert false;
}";
    string solverProcessName = $"z3-{DafnyOptions.DefaultZ3Version}";
    var processes1 = GetCurrentZ3Processes();
    var documentItem = CreateTestDocument(source);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

    await GetLastDiagnostics(documentItem, CancellationToken);
    var processes2 = GetCurrentZ3Processes();
    Assert.Equal(processes1 + 1, processes2);
    ApplyChange(ref documentItem, new Range(0, 0, 0, 0), "\n");
    await GetLastDiagnostics(documentItem, CancellationToken);
    var processes3 = GetCurrentZ3Processes();
    Assert.Equal(processes2, processes3);
  }
}
