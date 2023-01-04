using System;
using System.IO;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.VisualStudio.TestTools.UnitTesting;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various;

[TestClass]
public class IncludeFileTest : ClientBasedLanguageServerTest {

  [TestMethod]
  public async Task MethodWhosePostConditionFailsAndDependsOnIncludedFile() {
    var temp = (Path.GetTempFileName() + ".dfy").Replace("\\", "/");
    Console.WriteLine("temp file is: " + temp);
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
    Assert.AreEqual(1, verificationDiagnostics.Length, verificationDiagnostics.Stringify());
    await AssertNoDiagnosticsAreComing(CancellationToken);
  }
}
