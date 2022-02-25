using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Diagnostics;

[TestClass]
public class SimpleLinearVerificationDiagnosticTester : LinearVerificationDiagnosticTester {
  [TestMethod]
  public async Task EnsureVerificationDiagnosticsAreWorking() {
    var codeAndTrace = @"
    : s  s  s  |  v  v  v  v  | :predicate Ok() {
    : s  s  s  |  v  v  v  v  | :  true
    : s  s  s  |  v  v  v  v  | :}
    : ?  ?  ?  |  v  v  v  v  | :
    : s  S | || ||s||s||S| |  | :method Test(x: bool) returns (i: int)
    : s  S |=||=||-||-||~| |  | :   ensures i == 2
    : s  S | || ||s||s||S| |  | :{
    : s  S | || ||s||s||S| |  | :  if x {
    : s  S | || ||s||s||S| |  | :    i := 2;
    : s  S |=||=||-||-||~| |  | :  } else {
    : s  S | || |/!\|s||S| |  | :    i := 1;
    : s  S | || ||s||s||S| |  | :  }
    : s  S | || ||s||s||S| |  | :}
    : ?  ?  ?  |  v  v  v  |  | :    
    : s  s  s  |  v  v  v  v  | :predicate OkBis() {
    : s  s  s  |  v  v  v  v  | :  false
    : s  s  s  |  v  v  v  v  | :}".StripMargin();
    var code = ExtractCode(codeAndTrace);
    var documentItem = CreateTestDocument(code);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var traces1 = await GetAllLineVerificationDiagnostics(documentItem);
    ApplyChange(ref documentItem, new Range(10, 9, 10, 10), "/");
    var traces2 = await GetAllLineVerificationDiagnostics(documentItem);
    ApplyChange(ref documentItem, new Range(10, 9, 10, 10), "2");
    var traces3 = await GetAllLineVerificationDiagnostics(documentItem);

    var expected = RenderTrace(traces1.Concat(traces2).Concat(traces3).ToList(), code);
    AssertWithDiff.Equal(codeAndTrace, expected);

  }
}