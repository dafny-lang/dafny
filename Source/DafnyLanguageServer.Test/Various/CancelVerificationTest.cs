using System;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;
using Xunit.Abstractions;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various {
  public class CancelVerificationTest : ClientBasedLanguageServerTest {

    [Fact]
    public async Task ChangingTheDocumentStopsOnChangeVerification() {
      await SetUp(options => {
        options.Set(BoogieOptionBag.Cores, 2U);
      });
      var documentItem = CreateTestDocument(SlowToVerify2, "ChangingTheDocumentStopsOnChangeVerification.dfy");
      client.OpenDocument(documentItem);

      await WaitForStatus(new Range(11, 32, 11, 36), PublishedVerificationStatus.Running, CancellationToken);

      // Should cancel the previous request.
      ApplyChange(ref documentItem, new Range((12, 9), (12, 23)), "true");

      // Next line is only to gather more information for solving https://github.com/dafny-lang/dafny/issues/5436 
      await WaitUntilResolutionFinished(documentItem);

      await AssertNothingIsQueued(documentItem);
    }

    [Fact]
    public async Task ChangingTheDocumentStopsOnSaveVerification() {
      await SetUp(options => {
        options.Set(BoogieOptionBag.Cores, 2U);
        options.Set(ProjectManager.Verification, VerifyOnMode.Save);
      });
      var documentItem = CreateTestDocument(SlowToVerify2, "ChangingTheDocumentStopsOnSaveVerification.dfy");
      client.OpenDocument(documentItem);
      client.SaveDocument(documentItem);

      await WaitForStatus(new Range(11, 32, 11, 36), PublishedVerificationStatus.Running, CancellationToken);

      // Should cancel the previous request.
      ApplyChange(ref documentItem, new Range((12, 9), (12, 23)), "true");
      client.SaveDocument(documentItem);

      await AssertNothingIsQueued(documentItem);
    }

    [Fact]
    public async Task ChangingTheDocumentStopsManualVerification() {
      await SetUp(options => {
        options.Set(BoogieOptionBag.Cores, 2U);
        options.Set(ProjectManager.Verification, VerifyOnMode.Save);
      });
      var documentItem = CreateAndOpenTestDocument(SlowToVerify2, "ChangingTheDocumentStopsManualVerification.dfy");
      Assert.True(await client.RunSymbolVerification(documentItem, new Position(11, 34), CancellationToken));
      Assert.True(await client.RunSymbolVerification(documentItem, new Position(0, 23), CancellationToken));

      await WaitForStatus(new Range(11, 32, 11, 36), PublishedVerificationStatus.Running, CancellationToken);

      // Should cancel the previous request.
      ApplyChange(ref documentItem, new Range((12, 9), (12, 23)), "true");

      Assert.True(await client.RunSymbolVerification(documentItem, new Position(11, 34), CancellationToken));
      Assert.True(await client.RunSymbolVerification(documentItem, new Position(0, 23), CancellationToken));
      await AssertNothingIsQueued(documentItem);
    }

    private static string SlowToVerify2 =>
      @"
function {:unroll 100} Ack(m: nat, n: nat): nat
  decreases m, n
{
  if m == 0 then
    n + 1
  else if n == 0 then
    Ack(m - 1, 1)
  else
    Ack(m - 1, Ack(m, n - 1))
}

method {:resource_limit ""10e6""} test() {
  assert Ack(5, 5) == 0;
}".TrimStart();

    private async Task AssertNothingIsQueued(TextDocumentItem documentItem) {
      var status = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
      while (status.NamedVerifiables.Any(v => v.Status < PublishedVerificationStatus.Error)) {
        if (status.NamedVerifiables.Any(v => v.Status == PublishedVerificationStatus.Queued)) {
          var time = DateTime.Now;
          status = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
          var then = DateTime.Now;
          // A queued status may momentarily arise, while one task is being queued and the other being cancelled.
          if ((then - time).Milliseconds > 1000) {
            Assert.Fail("No task may be queued.");
          }
          continue;
        }

        status = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
      }
    }

    public CancelVerificationTest(ITestOutputHelper output) : base(output, LogLevel.Debug) {
    }
  }
}
