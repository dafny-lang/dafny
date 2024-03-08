using System.Diagnostics;
using System.IO.Pipelines;
using System.Reactive.Concurrency;
using System.Reflection;
using System.Text;
using Microsoft.Dafny;
using Microsoft.Extensions.Logging.Abstractions;
using OmniSharp.Extensions.JsonRpc;
using OmniSharp.Extensions.JsonRpc.Client;
using OmniSharp.Extensions.JsonRpc.Serialization;
using OmniSharp.Extensions.LanguageServer.Protocol.Client.Capabilities;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace DafnyDriver.Test;

public class FormatterCommandTest {
  [Fact]
  public async Task GitIssueVSCode452FormattingWorksOnBigFiles() {
    // We write to a temporary file
    var oneSource = (int i) => $@"function Test{i}(x: int): int
// This returns {i} if x is greater than 20
{{
  if x < 10 then
                  0
                  else if x < 20 then
                                       1
                                          else {i}
}}

";

    var oneSourceFormatted = (int i) => $@"function Test{i}(x: int): int
  // This returns {i} if x is greater than 20
{{
  if x < 10 then
    0
  else if x < 20 then
    1
  else {i}
}}

";
    var source = "";
    var sourceFormatted = "";
    for (var i = 0; i < 1000; i++) {
      source += oneSource(i);
      sourceFormatted += oneSourceFormatted(i);
    }

    var file = Path.GetTempFileName() + ".dfy";

    await File.WriteAllTextAsync(file, source);
    StringWriter strWriter = new StringWriter();
    var options = DafnyOptions.Create(strWriter, null,
      file
      );

    var exitValue = await FormatCommand.DoFormatting(options);
    Assert.Equal(0, (int)exitValue);

    var result = await File.ReadAllTextAsync(file);
    Assert.Equal(sourceFormatted, result);
    File.Delete(file);
  }
}
