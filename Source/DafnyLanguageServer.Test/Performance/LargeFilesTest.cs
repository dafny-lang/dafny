using System;
using System.Text;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Xunit;
using Xunit.Abstractions;
using Xunit.Sdk;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Performance;

public class LargeFilesTest : ClientBasedLanguageServerTest {
  protected override Task SetUp(Action<DafnyOptions> modifyOptions) {
    return base.SetUp(options => {
      modifyOptions?.Invoke(options);
      options.Set(ServerCommand.UpdateThrottling, ServerCommand.DefaultThrottleTime);
    });
  }

  /// <summary>
  /// To reduce runtime of this test,
  /// remove ReportRealtimeDiagnostics (since it is called 10 times for each update,
  /// and calls InitialIdeState, which often calls CompilationAfterResolution.ToIdeState (expensive))
  ///  
  /// To further reduce runtime, optimize DafnyProject.GetRootSourceUris (called for each update)
  /// </summary>
  [Fact]
  public async Task QuickEditsInLargeFile() {
    string GetLineContent(int index) => $"method Foo{index}() {{ assume false; }}";
    var contentBuilder = new StringBuilder();
    for (int lineNumber = 0; lineNumber < 1000; lineNumber++) {
      contentBuilder.AppendLine(GetLineContent(lineNumber));
    }
    var source = contentBuilder.ToString();

    Exception lastException = null;
    for (int attempt = 0; attempt < 5; attempt++) {
      try {
        var cancelSource = new CancellationTokenSource();
        var measurementTask = AssertThreadPoolIsAvailable(cancelSource.Token);
        var beforeOpen = DateTime.Now;
        var documentItem = await CreateAndOpenTestDocument(source, "ManyFastEditsUsingLargeFiles.dfy");
        var afterOpen = DateTime.Now;
        var openMilliseconds = (afterOpen - beforeOpen).Milliseconds;
        for (int i = 0; i < 100; i++) {
          ApplyChange(ref documentItem, new Range(0, 0, 0, 0), "// added this comment\n");
        }

        await client.WaitForNotificationCompletionAsync(documentItem.Uri, CancellationToken);
        var afterChange = DateTime.Now;
        var changeMilliseconds = (afterChange - afterOpen).Milliseconds;
        await AssertNoDiagnosticsAreComing(CancellationToken);
        cancelSource.Cancel();
        await measurementTask;
        Assert.True(changeMilliseconds < openMilliseconds * 3,
          $"changeMilliseconds {changeMilliseconds}, openMilliseconds {openMilliseconds}");

        // Commented code left in intentionally
        // await output.WriteLineAsync("openMilliseconds: " + openMilliseconds);
        // await output.WriteLineAsync("changeMilliseconds: " + changeMilliseconds);
        return;
      } catch (AssertActualExpectedException e) {
        lastException = e;
      }
    }

    throw lastException!;
  }

  private async Task AssertThreadPoolIsAvailable(CancellationToken durationToken, TimeSpan? maximumThreadPoolSchedulingTime = null) {
    int ticks = 0;
    var waitTime = 100;
    var start = DateTime.Now;
    while (!durationToken.IsCancellationRequested) {
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
    var maximumMilliseconds = maximumThreadPoolSchedulingTime?.Milliseconds ?? 10;
    Assert.True(averageTimeToSchedule < maximumMilliseconds);
  }

  public LargeFilesTest(ITestOutputHelper output) : base(output) {
  }
}