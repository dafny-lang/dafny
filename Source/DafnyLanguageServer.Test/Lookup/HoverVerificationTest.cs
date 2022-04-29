using System.Collections.Generic;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using JetBrains.Annotations;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.Extensions.Configuration;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.JsonRpc;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Lookup {
  [TestClass]
  public class HoverVerificationTest : DafnyLanguageServerTestBase {
    private const int MaxTestExecutionTimeMs = 10000;

    private ILanguageClient client;
    private TestNotificationReceiver<CompilationStatusParams> notificationReceiver;
    private IDictionary<string, string> configuration;

    [TestInitialize]
    public Task SetUp() => SetUp(null);

    public async Task SetUp(IDictionary<string, string> configuration) {
      this.configuration = configuration;
      notificationReceiver = new();
      client = await InitializeClient(options => {
        options
          .AddHandler(DafnyRequestNames.CompilationStatus, NotificationHandler.For<CompilationStatusParams>(notificationReceiver.NotificationReceived));
      });
    }

    protected override IConfiguration CreateConfiguration() {
      return configuration == null
        ? base.CreateConfiguration()
        : new ConfigurationBuilder().AddInMemoryCollection(configuration).Build();
    }

    [TestMethod, Timeout(MaxTestExecutionTimeMs)]
    public async Task HoverGetsBasicAssertionInformation() {
      var documentItem = await GetDocumentItem(@"
method Abs(x: int) returns (y: int)
//     ^ hover #2
    ensures y >= 0
{ //           ^ hover #1
  if x < 2 {
    return -x;
  }
  return x;
}
", CompilationStatus.VerificationFailed);
      await AssertHoverMatches(documentItem, (2, 15),
        @"assertion of [batch](???) #1/1 checked in ???ms with ??? resource count:  
`testFile0.dfy(6, 5): `*A postcondition might not hold on this return path.*"
      );
      await AssertHoverMatches(documentItem, (0, 7),
        @"**Abs** metrics:

???ms in 1 [assertion batch](???)  
??? resource count"
      );
    }

    private async Task<TextDocumentItem> GetDocumentItem(string source, CompilationStatus expectedStatus) {
      source = source.TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var lastStatus = await WaitUntilDafnyFinishes(documentItem);
      Assert.AreEqual(expectedStatus, lastStatus);
      return documentItem;
    }

    private async Task AssertHoverMatches(TextDocumentItem documentItem, Position hoverPosition, string expected) {
      var hover = await RequestHover(documentItem, hoverPosition);
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.IsNotNull(markup);
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      AssertMatchRegex(expected, markup.Value);
    }

    private void AssertMatchRegex(string expected, string value) {
      var regexExpected = Regex.Escape(expected).Replace(@"\?\?\?", ".+");
      Assert.IsTrue(new Regex(regexExpected).Match(value).Success, "{0} did not match {1}", value, regexExpected);
    }

    private async Task<CompilationStatus> WaitUntilDafnyFinishes(TextDocumentItem documentItem) {
      CompilationStatusParams lastResult;
      do {
        lastResult = await notificationReceiver.AwaitNextNotificationAsync(CancellationToken);
        Assert.AreEqual(documentItem.Uri, lastResult.Uri);
        Assert.AreEqual(documentItem.Version, lastResult.Version);
      } while (lastResult.Status != CompilationStatus.VerificationFailed &&
               lastResult.Status != CompilationStatus.VerificationSucceeded &&
               lastResult.Status != CompilationStatus.ParsingFailed &&
               lastResult.Status != CompilationStatus.ResolutionFailed);

      return lastResult.Status;
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
  }
}
