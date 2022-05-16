using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.JsonRpc;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Diagnostics;

[TestClass]
public class ConcurrentLinearVerificationDiagnosticTester : LinearVerificationDiagnosticTester {
  private const int MaxSimultaneousVerificationTasks = 3;

  protected DiagnosticsReceiver[] diagnosticsReceivers = new DiagnosticsReceiver[MaxSimultaneousVerificationTasks];
  protected TestNotificationReceiver<VerificationStatusGutter>[] verificationDiagnosticsReceivers =
    new TestNotificationReceiver<VerificationStatusGutter>[MaxSimultaneousVerificationTasks];

  private void NotifyAllDiagnosticsReceivers(PublishDiagnosticsParams request) {
    foreach (var receiver in diagnosticsReceivers) {
      receiver.NotificationReceived(request);
    }
  }

  private void NotifyAllVerificationDiagnosticsReceivers(VerificationStatusGutter request) {
    foreach (var receiver in verificationDiagnosticsReceivers) {
      receiver.NotificationReceived(request);
    }
  }

  [TestInitialize]
  public override async Task SetUp() {
    for (var i = 0; i < diagnosticsReceivers.Length; i++) {
      diagnosticsReceivers[i] = new();
      verificationDiagnosticsReceivers[i] = new();
    }
    verificationDiagnosticsReceiver = new();
    client = await InitializeClient(options =>
      options
        .OnPublishDiagnostics(NotifyAllDiagnosticsReceivers)
        .AddHandler(DafnyRequestNames.VerificationStatusGutter,
          NotificationHandler.For<VerificationStatusGutter>(NotifyAllVerificationDiagnosticsReceivers))
    );
  }

  [TestMethod/*, Timeout(MaxTestExecutionTimeMs)*/]
  public async Task EnsuresManyDocumentsCanBeVerifiedAtOnce() {
    var result = new List<Task>();
    for (var i = 0; i < MaxSimultaneousVerificationTasks; i++) {
      result.Add(VerifyTrace(@"
 .  |  |  |  I  |  | :predicate F(i: int) {
 .  |  |  |  I  |  | :  false // Should not be highlighted in gutter.
 .  |  |  |  I  |  | :}
    |  |  |  I  |  | :
 .  S [S][ ][I][S][ ]:method H()
 .  S [=][=][-][~][O]:  ensures F(1)
 .  S [=][=][-][~][=]:{//Next: { assert false;
 .  S [S][ ][I][S][ ]:}", $"testfile{i}.dfy", true, diagnosticsReceivers[i], verificationDiagnosticsReceivers[i]));
    }

    for (var i = 0; i < MaxSimultaneousVerificationTasks; i++) {
      await result[i];
    }

    //await Task.WhenAll(result.ToArray());
  }

}