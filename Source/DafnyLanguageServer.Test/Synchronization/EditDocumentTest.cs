using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization;

public class EditDocumentTest : ClientBasedLanguageServerTest {

  [Fact]
  public async Task SlowlyTypeFile() {
    var source = @"function Foo<T>(): seq<T>";
    var document = CreateAndOpenTestDocument("");

    var index = 0;
    foreach (var c in source) {
      ApplyChange(ref document, new Range(0, index, 0, index), c.ToString());
      index++;
      var completionItems = await RequestCompletionAsync(document, new Position(0, index));
      var hover = await RequestHover(document, new Position(0, index));
    }

    var diagnostic = await GetLastDiagnostics(document);
    Assert.Empty(diagnostic);
  }

  private Task<Hover> RequestHover(TextDocumentItem documentItem, Position position) {
    return client.RequestHover(
      new HoverParams {
        TextDocument = documentItem.Uri,
        Position = position
      },
      CancellationToken
    );
  }

  private async Task<List<CompletionItem>> RequestCompletionAsync(TextDocumentItem documentItem, Position position) {
    // TODO at this time we do not set the context since it appears that's also the case when used within VSCode.
    var completionList = await client.RequestCompletion(
      new CompletionParams {
        TextDocument = documentItem.Uri,
        Position = position
      },
      CancellationToken
    ).AsTask();
    return completionList.OrderBy(completion => completion.Label).ToList();
  }

  public EditDocumentTest(ITestOutputHelper output, LogLevel dafnyLogLevel = LogLevel.Information) : base(output, dafnyLogLevel) {
  }
}