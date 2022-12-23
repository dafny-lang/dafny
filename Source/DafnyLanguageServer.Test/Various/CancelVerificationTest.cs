using System;
using System.Collections.Generic;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various {
  [TestClass]
  public class CancelVerificationTest : ClientBasedLanguageServerTest {

    [TestMethod]
    public async Task ChangingTheDocumentStopsOnChangeVerification() {
      await SetUp(options => {
        options.Set(BoogieOptionBag.Cores, 2);
      });
      var documentItem = CreateTestDocument(SlowToVerify2);
      client.OpenDocument(documentItem);

      await WaitForStatus(new Range(11, 23, 11, 27), PublishedVerificationStatus.Running, CancellationToken);

      // Should cancel the previous request.
      ApplyChange(ref documentItem, new Range((12, 9), (12, 23)), "true");
      await AssertNothingIsQueued(documentItem);
    }

    [TestMethod]
    public async Task ChangingTheDocumentStopsOnSaveVerification() {
      await SetUp(options => {
        options.Set(BoogieOptionBag.Cores, 2);
        options.Set(ServerCommand.Verification, VerifyOnMode.Save);
      });
      var documentItem = CreateTestDocument(SlowToVerify2);
      client.OpenDocument(documentItem);
      client.SaveDocument(documentItem);

      await WaitForStatus(new Range(11, 23, 11, 27), PublishedVerificationStatus.Running, CancellationToken);

      // Should cancel the previous request.
      ApplyChange(ref documentItem, new Range((12, 9), (12, 23)), "true");
      client.SaveDocument(documentItem);

      await AssertNothingIsQueued(documentItem);
    }

    [TestMethod]
    public async Task ChangingTheDocumentStopsManualVerification() {
      await SetUp(options => {
        options.Set(BoogieOptionBag.Cores, 2);
        options.Set(ServerCommand.Verification, VerifyOnMode.Save);
      });
      var documentItem = CreateTestDocument(SlowToVerify2);
      client.OpenDocument(documentItem);
      Assert.IsTrue(await client.RunSymbolVerification(documentItem, new Position(11, 23), CancellationToken));
      Assert.IsTrue(await client.RunSymbolVerification(documentItem, new Position(0, 30), CancellationToken));

      await WaitForStatus(new Range(11, 23, 11, 27), PublishedVerificationStatus.Running, CancellationToken);

      // Should cancel the previous request.
      ApplyChange(ref documentItem, new Range((12, 9), (12, 23)), "true");

      Assert.IsTrue(await client.RunSymbolVerification(documentItem, new Position(11, 23), CancellationToken));
      Assert.IsTrue(await client.RunSymbolVerification(documentItem, new Position(0, 30), CancellationToken));
      await AssertNothingIsQueued(documentItem);
    }

    private static string SlowToVerify2 =>
      @"
function method {:unroll 100} Ack(m: nat, n: nat): nat
  decreases m, n
{
  if m == 0 then
    n + 1
  else if n == 0 then
    Ack(m - 1, 1)
  else
    Ack(m - 1, Ack(m, n - 1))
}

method {:timeLimit 10} test() {
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
  }
}
