using System;
using System.Diagnostics.Metrics;
using System.IO;
using System.Reactive;
using System.Reactive.Linq;
using System.Reactive.Subjects;
using System.Reactive.Threading.Tasks;
using System.Text;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Extensions.Logging;
using Xunit;
using Xunit.Abstractions;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Performance;

public class LargeFilesTest : ClientBasedLanguageServerTest {

  [Fact]
  public async Task SlowEditsUsingLargeFilesAndIncludes() {
    var directory = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName());
    Directory.CreateDirectory(directory);
    var filePath = await CreateLargeFile(directory);
    var source = @$"include ""{filePath}""";
    var documentItem = await CreateAndOpenTestDocument(source);
    for (int i = 0; i < 20; i++) {
      await Task.Delay(200);
      ApplyChange(ref documentItem, new Range(0, 0, 0, 0), "// added this comment\n");
    }
    await client.WaitForNotificationCompletionAsync(documentItem.Uri, CancellationToken);
    await AssertNoDiagnosticsAreComing(CancellationToken);
    Directory.Delete(directory, true);
  }

  private static async Task<string> CreateLargeFile(string directory) {
    var filePath = Path.Combine(directory, "large.dfy");
    var file = new StreamWriter(filePath);
    string GetLineContent(int index) => $"method Foo{index}() {{ assume false; }}";
    for (int lineNumber = 0; lineNumber < 10000; lineNumber++) {
      await file.WriteLineAsync(GetLineContent(lineNumber));
    }

    file.Close();
    return filePath;
  }

  [Fact]
  public async Task ManyFastEditsUsingLargeFilesAndIncludes() {
    var directory = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName());
    Directory.CreateDirectory(directory);
    var filePath = await CreateLargeFile(directory);
    var source = @$"include ""{filePath}""";
    var documentItem = await CreateAndOpenTestDocument(source, Path.Combine(Directory.GetCurrentDirectory(), "Performance/TestFiles/test.dfy"));
    for (int i = 0; i < 100; i++) {
      ApplyChange(ref documentItem, new Range(0, 0, 0, 0), "// added this comment\n");
    }

    await client.WaitForNotificationCompletionAsync(documentItem.Uri, CancellationToken);
    await AssertNoDiagnosticsAreComing(CancellationToken);
    Directory.Delete(directory, true);
  }

  [Fact]
  public async Task QuickEditsInLargeFile() {
    string GetLineContent(int index) => $"method Foo{index}() {{ assume false; }}";
    var contentBuilder = new StringBuilder();
    for (int lineNumber = 0; lineNumber < 1000; lineNumber++) {
      contentBuilder.AppendLine(GetLineContent(lineNumber));
    }
    var source = contentBuilder.ToString();

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
    Assert.True(changeMilliseconds < openMilliseconds * 3);
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