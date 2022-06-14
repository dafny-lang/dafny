using System;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Configuration;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization {
  [TestClass]
  public class StressDiagnosticsTest : ClientBasedLanguageServerTest {
    private const int MinEditSpeed = 100;
    private const int MaxEditSpeed = 600;
    private const int MaxTests = 10;
    // We are waiting two times on each `waiting time`, so the total waiting time is
    // MaxTests *  (MaxEditSpeed + MinEditSpeed)
    // which, given the above constants, is 10*700 = 7 seconds.
    // In practice, waiting for verification as well makes this test finish in 20-30 seconds

    /// <summary>
    ///  This test changes method M3() by first introducing a typo, then removing it as well as with its assert,
    /// then re-adding the assert again, under various waiting times.
    /// </summary>
    [TestMethod]
    public async Task ModifyingAComplexDocumentSeveralTimesDoesNotPreventDiagnosticsFromComing() {
      var source = @"
function fib(n: nat): int
  decreases n
{
  if n <= 1 then 1
  else fib(n - 1) + fib(n - 2)
}

method M0() {
  assert fib(00) != -1;
}
method M1() {
  assert fib(10) != -1;
}
method M2() {
  assert fib(20) == -1;
}
method M3() {
  assert fib(30) == -1;
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

      var diagnostics = await GetLastDiagnostics(documentItem, CancellationToken);
      Assert.AreEqual(2, diagnostics.Length);
      for (var i = 0; i < MaxTests; i++) {
        var waitingTime = ((MaxEditSpeed - MinEditSpeed) * i / (MaxTests - 1)) + MinEditSpeed;
        //await Console.Out.WriteLineAsync($"Test {i + 1}/{MaxTests}, delay is {waitingTime}ms, starting...");
        ApplyChange(ref documentItem, ((17, 0), (17, 0)), "/"); // Typo, resets the diagnostics
        diagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
        Assert.AreEqual(1, diagnostics.Count(diagnostic => diagnostic.Source == MessageSource.Parser.ToString()));
        await Task.Delay(waitingTime);
        ApplyChange(ref documentItem, ((17, 0), (17, 24)), ""); // Remove the typo and verification error
        await Task.Delay(waitingTime);
        ApplyChange(ref documentItem, ((17, 0), (17, 0)), "  assert fib(30) == -1;"); // Re-add the verification error
        //await Console.Out.WriteLineAsync($"waiting for diagnostics...");
        diagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
        //await DisplayDiagnostics(diagnostics, "after removing the typo");
        Assert.AreEqual(1, diagnostics.Length);
        diagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
        //await DisplayDiagnostics(diagnostics, "after reinserting the error");
        Assert.AreEqual(2, diagnostics.Length);
      }
    }
  }
}
