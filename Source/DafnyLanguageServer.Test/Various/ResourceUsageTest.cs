using System.Diagnostics;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various;

[TestClass]
public class ResourceUsageTest : ClientBasedLanguageServerTest {

  [TestMethod]
  public async Task SolverProcessCountDoesNotIncreaseOnEachVerification() {
    var source = @"
method Foo()
{
    assert false;
}";
    const string solverProcessName = "z3-4.8.5";
    var processes1 = Process.GetProcessesByName(solverProcessName);
    var documentItem = CreateTestDocument(source);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

    await GetLastDiagnostics(documentItem, CancellationToken);
    var processes2 = Process.GetProcessesByName(solverProcessName);
    Assert.IsTrue(processes2.Length <= processes1.Length);
    ApplyChange(ref documentItem, new Range(0, 0, 0, 0), "\n");
    await GetLastDiagnostics(documentItem, CancellationToken);
    var processes3 = Process.GetProcessesByName(solverProcessName);
    Assert.IsTrue(processes3.Length <= processes2.Length);
  }
}
