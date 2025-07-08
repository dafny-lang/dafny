﻿using System;
using System.Collections.Generic;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.JsonRpc;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.GutterStatus;

[Collection("Sequential Collection")] // Because this class contains tests that can easily time out
public class ConcurrentLinearVerificationGutterStatusTester : LinearVerificationGutterStatusTester {
  private const int MaxSimultaneousVerificationTasks = 5;

  protected TestNotificationReceiver<VerificationStatusGutter>[] verificationStatusGutterReceivers =
    new TestNotificationReceiver<VerificationStatusGutter>[MaxSimultaneousVerificationTasks];

  private void NotifyAllVerificationGutterStatusReceivers(VerificationStatusGutter request) {
    foreach (var receiver in verificationStatusGutterReceivers) {
      receiver.NotificationReceived(request);
    }
  }

  protected override async Task SetUp(Action<DafnyOptions> modifyOptions) {
    for (var i = 0; i < verificationStatusGutterReceivers.Length; i++) {
      verificationStatusGutterReceivers[i] = new(logger);
    }
    verificationStatusGutterReceiver = new(logger);
    (client, Server) = await Initialize(options =>
      options
        .AddHandler(DafnyRequestNames.VerificationStatusGutter,
          NotificationHandler.For<VerificationStatusGutter>(NotifyAllVerificationGutterStatusReceivers))
    , o => {
      o.Set(GutterIconAndHoverVerificationDetailsManager.LineVerificationStatus, true);
      modifyOptions?.Invoke(o);
    });
  }

  [Fact]
  public async Task EnsuresManyDocumentsCanBeVerifiedAtOnce() {
    var result = new List<Task>();
    // Every verificationStatusGutterReceiver checks that the filename matches and filters out notifications that do not match.
    // That way, it can rebuild the trace for every file independently.
    for (var i = 0; i < MaxSimultaneousVerificationTasks; i++) {
      result.Add(VerifyTrace(@"
 .  |  |  |  I  |  |  | :predicate F(i: int) {
 .  |  |  |  I  |  |  | :  false // Should not be highlighted in gutter.
 .  |  |  |  I  |  |  | :}
    |  |  |  I  |  |  | :
 .  .  S [ ][I][I][S][ ]:method H()
 .  .  S [=][-][-][~][O]:  ensures F(1)
 .  .  S [=][-][-][~][=]:{//Replace: { assert false;
 .  .  S [ ][I][I][S][ ]:}", false, $"EnsuresManyDocumentsCanBeVerifiedAtOnce{i}.dfy", true, true, verificationStatusGutterReceivers[i]));
    }

    for (var i = 0; i < MaxSimultaneousVerificationTasks; i++) {
      await result[i];
    }
  }

  public ConcurrentLinearVerificationGutterStatusTester(ITestOutputHelper output) : base(output) {
  }
}
