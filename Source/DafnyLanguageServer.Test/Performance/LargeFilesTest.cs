using System;
using System.IO;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Extensions.Logging;
using Xunit;
using Xunit.Abstractions;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Performance;

public class LargeFiles : ClientBasedLanguageServerTest {

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

  private static async Task<string> CreateLargeFile(string directory)
  {
    var filePath = Path.Combine(directory, "large.dfy");
    var file = new StreamWriter(filePath);
    string GetLineContent(int index) => $"method Foo{index}() {{ assume false; }}";
    for (int lineNumber = 0; lineNumber < 10000; lineNumber++)
    {
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
    for (int i = 0; i < 1000; i++) {
      ApplyChange(ref documentItem, new Range(0, 0, 0, 0), "// added this comment\n");
    }

    await client.WaitForNotificationCompletionAsync(documentItem.Uri, CancellationToken);
    await AssertNoDiagnosticsAreComing(CancellationToken);
    Directory.Delete(directory, true);
  }

  public LargeFiles(ITestOutputHelper output) : base(output, LogLevel.Debug) {
  }
}