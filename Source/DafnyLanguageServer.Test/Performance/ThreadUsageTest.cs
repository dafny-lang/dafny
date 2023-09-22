using System;
using System.Diagnostics;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Extensions.Logging;
using Xunit;
using Xunit.Abstractions;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Performance; 

[Collection("Sequential Collection")]  // Seems to deadlock when run in parallel
public class ThreadUsageTest : ClientBasedLanguageServerTest {

  [Fact]
  public async Task NoExtraThreadAfterEachChange() {
    var source = "method Foo() { assert false; }";
    var document = await CreateOpenAndWaitForResolve(source);
    var threadCountBefore = Process.GetCurrentProcess().Threads.Count;
    for (var i = 0; i < 10; i++) {
      ApplyChange(ref document, new Range(0, 0, 0, 0), "//comment" + Environment.NewLine);
      await GetLastDiagnostics(document);
    }
    var threadCountAfter = Process.GetCurrentProcess().Threads.Count;
    const int maxThreadCountIncrease = 5;
    Assert.True(threadCountAfter - threadCountBefore < maxThreadCountIncrease);
  }

  public ThreadUsageTest(ITestOutputHelper output, LogLevel dafnyLogLevel = LogLevel.Information)
    : base(output, dafnyLogLevel) {
  }
}