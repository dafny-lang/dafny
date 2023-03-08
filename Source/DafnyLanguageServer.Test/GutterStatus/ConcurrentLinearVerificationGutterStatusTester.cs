using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.JsonRpc;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit.Abstractions;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Diagnostics;

[TestClass]
public class ConcurrentLinearVerificationGutterStatusTester : LinearVerificationGutterStatusTester {
  private const int MaxSimultaneousVerificationTasks = 5;

  protected TestNotificationReceiver<VerificationStatusGutter>[] verificationStatusGutterReceivers =
    new TestNotificationReceiver<VerificationStatusGutter>[MaxSimultaneousVerificationTasks];

  private void NotifyAllVerificationGutterStatusReceivers(VerificationStatusGutter request) {
    foreach (var receiver in verificationStatusGutterReceivers) {
      receiver.NotificationReceived(request);
    }
  }

  public override async Task SetUp(Action<DafnyOptions> modifyOptions) {
    for (var i = 0; i < verificationStatusGutterReceivers.Length; i++) {
      verificationStatusGutterReceivers[i] = new();
    }
    verificationStatusGutterReceiver = new();
    client = await InitializeClient(options =>
      options
        .AddHandler(DafnyRequestNames.VerificationStatusGutter,
          NotificationHandler.For<VerificationStatusGutter>(NotifyAllVerificationGutterStatusReceivers))
    , o => {
      o.Set(ServerCommand.LineVerificationStatus, true);
      modifyOptions?.Invoke(o);
    });
  }

  [TestMethod]
  public async Task EnsuresManyDocumentsCanBeVerifiedAtOnce() {
    var result = new List<Task>();
    // Every verificationStatusGutterReceiver checks that the filename matches and filters out notifications that do not match.
    // That way, it can rebuild the trace for every file independently.
    for (var i = 0; i < MaxSimultaneousVerificationTasks; i++) {
      result.Add(VerifyTrace(@"
 .  |  |  |  I  |  | :predicate F(i: int) {
 .  |  |  |  I  |  | :  false // Should not be highlighted in gutter.
 .  |  |  |  I  |  | :}
    |  |  |  I  |  | :
 .  S [S][ ][I][S][ ]:method H()
 .  S [=][=][-][~][O]:  ensures F(1)
 .  S [=][=][-][~][=]:{//Next: { assert false;
 .  S [S][ ][I][S][ ]:}", $"testfile{i}.dfy", true, verificationStatusGutterReceivers[i]));
    }

    for (var i = 0; i < MaxSimultaneousVerificationTasks; i++) {
      await result[i];
    }
  }

  public ConcurrentLinearVerificationGutterStatusTester(ITestOutputHelper output) : base(output)
  {
  }
}
