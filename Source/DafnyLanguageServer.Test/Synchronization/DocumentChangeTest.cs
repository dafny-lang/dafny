using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization;

public class DocumentChangeTest : ClientBasedLanguageServerTest {

  [Fact]
  public async Task ChangeRangeOutOfBounds() {
    var source = "method Foo() {}\n";
    var documentItem = CreateAndOpenTestDocument(source);
    ApplyChanges(ref documentItem, new List<Change>() {
      new(new Range(0,0,1,0), ""),
      new(new Range(0,2,0,4), "blaaa")
    });
    while (true) {
      var telemetry = await telemetryReceiver.AwaitNextNotificationAsync(CancellationToken);
      var found = telemetry.ExtensionData.Any(t =>
        t is { Key: "payload", Value: string message } && message.Contains("does not fall within the document range"));
      if (found) {
        break;
      }
    }
  }

  public DocumentChangeTest(ITestOutputHelper output, LogLevel dafnyLogLevel = LogLevel.Information) : base(output, dafnyLogLevel) {
  }
}