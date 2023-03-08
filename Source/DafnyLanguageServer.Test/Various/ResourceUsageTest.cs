using System.Diagnostics;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit.Abstractions;

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
    string solverProcessName = $"z3-{DafnyOptions.DefaultZ3Version}";
    var processes1 = Process.GetProcessesByName(solverProcessName);
    var documentItem = CreateTestDocument(source);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

    await GetLastDiagnostics(documentItem, CancellationToken);
    var processes2 = Process.GetProcessesByName(solverProcessName);
    Assert.AreEqual(processes1.Length, processes2.Length - 1);
    ApplyChange(ref documentItem, new Range(0, 0, 0, 0), "\n");
    await GetLastDiagnostics(documentItem, CancellationToken);
    var processes3 = Process.GetProcessesByName(solverProcessName);
    Assert.AreEqual(processes2.Length, processes3.Length);
  }

  public ResourceUsageTest(ITestOutputHelper output) : base(output)
  {
  }
}
