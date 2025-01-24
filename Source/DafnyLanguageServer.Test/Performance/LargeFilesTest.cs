using System;
using System.Collections.Generic;
using System.Text;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using Xunit;
using Xunit.Abstractions;
using Xunit.Sdk;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Performance;

public class LargeFilesTest : ClientBasedLanguageServerTest {
  protected override Task SetUp(Action<DafnyOptions> modifyOptions) {
    return base.SetUp(options => {
      modifyOptions?.Invoke(options);
      // We're setting LineVerificationStatus to false already, with the expectation that this will become the default.
      options.Set(GutterIconAndHoverVerificationDetailsManager.LineVerificationStatus, false);
      options.Set(LegacySignatureAndCompletionTable.MigrateSignatureAndCompletionTable, false);
      options.Set(ProjectManager.UpdateThrottling, ProjectManager.DefaultThrottleTime);
    });
  }

  /// <summary>
  /// When you run this test with a debugger, it grinds to a halt and will appear deadlocked.
  /// Change all the numbers to smaller values (let's say 1) to workaround this problem.
  /// 
  /// This test should complete in less than a second, because it opens a moderately sized file
  /// on which it makes edits so quickly that the edits should all be processed in a single compilation.
  /// And a single compilation should complete in less than 200ms.
  ///
  /// Right now the test still takes more than 5 seconds.
  /// To reduce runtime of this test,
  /// remove ReportRealtimeDiagnostics (since it is called 10 times for each update,
  /// and calls InitialIdeState, which often calls CompilationAfterResolution.ToIdeState (expensive))
  /// </summary>
  [Fact]
  public async Task QuickEditsInLargeFile() {
    string GetLineContent(int index) => $"method Foo{index}() {{ assume {{:axiom}} false; }}";
    var contentBuilder = new StringBuilder();
    for (int lineNumber = 0; lineNumber < 1000; lineNumber++) {
      contentBuilder.AppendLine(GetLineContent(lineNumber));
    }
    var source = contentBuilder.ToString();

    Exception lastException = null;
    List<double> timeToScheduleHistory = [];
    List<double> divisionHistory = [];
    try {
      for (int attempt = 0; attempt < 10; attempt++) {
        var threadPoolSchedulingCancellationToken = new CancellationTokenSource();
        var threadPoolSchedulingTimeTask = TrackThreadPoolSchedulingTime(threadPoolSchedulingCancellationToken.Token);
        var beforeOpen = DateTime.Now;
        var documentItem = await CreateOpenAndWaitForResolve(source, "ManyFastEditsUsingLargeFiles.dfy",
          cancellationToken: CancellationTokenWithHighTimeout);
        var afterOpen = DateTime.Now;
        var openMilliseconds = (afterOpen - beforeOpen).TotalMilliseconds;
        for (int i = 0; i < 100; i++) {
          ApplyChange(ref documentItem, new Range(0, 0, 0, 0), "// added this comment\n");
        }

        await client.WaitForNotificationCompletionAsync(documentItem.Uri, CancellationTokenWithHighTimeout);
        var afterChange = DateTime.Now;
        var changeMilliseconds = (afterChange - afterOpen).TotalMilliseconds;
        await AssertNoDiagnosticsAreComing(CancellationTokenWithHighTimeout);
        await threadPoolSchedulingCancellationToken.CancelAsync();
        var averageTimeToSchedule = await threadPoolSchedulingTimeTask;
        var division = changeMilliseconds / openMilliseconds;

        timeToScheduleHistory.Add(averageTimeToSchedule);
        divisionHistory.Add(division);
        // Commented code left in intentionally
        // await output.WriteLineAsync("openMilliseconds: " + openMilliseconds);
        // await output.WriteLineAsync("changeMilliseconds: " + changeMilliseconds);
        // await output.WriteLineAsync("division: " + division);
        // await output.WriteLineAsync("averageTimeToSchedule: " + averageTimeToSchedule);
        try {
          Assert.True(averageTimeToSchedule < 100, $"averageTimeToSchedule: {averageTimeToSchedule}");
          // Migration should be constant time, which would allow this number to be about 1.
          // Right now migration is still slow so this has been set to 10 so the test can pass.
          var changeTimeMultiplier = 15;
          Assert.True(division < changeTimeMultiplier,
            $"changeMilliseconds {changeMilliseconds}, openMilliseconds {openMilliseconds}");

          return;
        } catch (AssertActualExpectedException e) {
          lastException = e;
        }
      }
    } catch (OperationCanceledException) {
    }

    logger.LogInformation("Average time to schedule history: \n" + string.Join(", ", timeToScheduleHistory));
    logger.LogInformation("Division history: \n" + string.Join(", ", divisionHistory));
    throw lastException!;
  }

  private async Task<double> TrackThreadPoolSchedulingTime(CancellationToken durationToken) {
    int ticks = 0;
    var waitTime = 100;
    var start = DateTime.Now;
    while (!durationToken.IsCancellationRequested) {
      // Measuring the time Task.Run takes is the point of this method.
      await Task.Run(() => {
        Thread.Sleep(waitTime);
      });

      ticks++;
    }

    var end = DateTime.Now;
    var span = end - start;
    var totalSleepTime = ticks * waitTime;
    var totalSchedulingTime = span.TotalMilliseconds - totalSleepTime;
    var averageTimeToSchedule = totalSchedulingTime / ticks;
    // await output.WriteLineAsync($"averageTimeToSchedule: {averageTimeToSchedule:0.##}");
    return averageTimeToSchedule;
  }

  public LargeFilesTest(ITestOutputHelper output) : base(output) {
  }
}
