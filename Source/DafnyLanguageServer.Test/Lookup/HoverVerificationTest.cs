﻿using System.Collections.Generic;
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
//     ^ Hover #4
    ensures y >= 0
{ //           ^ hover #1
  if x < 2 { // Hover #2 on the brace
    return -x;
  }
  assert x > 2; // Hover #3 on the '>'
  return x;
}
", "testFile.dfy", CompilationStatus.VerificationFailed);
      // When hovering the postcondition, it should display the position of the failing path
      await AssertHoverMatches(documentItem, (2, 15),
        @"assertion #1/2 of [batch](???) #1/1 checked in ???ms with ??? resource count:  
`testFile.dfy(6, 5): `*A postcondition might not hold on this return path.*"
      );
      // When hovering the failing path, it does not display the position of the failing postcondition
      // because the IDE extension already does it.
      await AssertHoverMatches(documentItem, (5, 4),
        @"assertion #1/2 of [batch](???) #1/1 checked in ???ms with ??? resource count:  
*A postcondition might not hold on this return path.*"
      );
      await AssertHoverMatches(documentItem, (7, 11),
        @"assertion #2/2 of [batch](???) #1/1 checked in ???ms with ??? resource count:  
*assertion might not hold*"
      );
      await AssertHoverMatches(documentItem, (0, 7),
        @"**Abs** metrics:

???ms in 1 [assertion batch](???)  
??? resource count"
      );
    }

    [TestMethod, Timeout(MaxTestExecutionTimeMs)]
    public async Task BetterMessageWhenOneAssertPerBatch() {
      var documentItem = await GetDocumentItem(@"
method {:vcs_split_on_every_assert} f(x: int) {
  assert x >= 2; // Hover #1
  assert x >= 1; // Hover #2
}
", "testfile.dfy", CompilationStatus.VerificationFailed);
      await AssertHoverMatches(documentItem, (1, 12),
        @"assertion of [batch](???) #???/2 checked in ???ms with ??? resource count:  
*assertion might not hold*"
      );
      await AssertHoverMatches(documentItem, (2, 12),
        @"assertion of [batch](???) #???/2 checked in ???ms with ??? resource count:  
*assertion always holds*"
      );
    }

    [TestMethod, Timeout(MaxTestExecutionTimeMs)]
    public async Task MeaningfulMessageWhenMethodWithoutAssert() {
      var documentItem = await GetDocumentItem(@"
method f(x: int) {
  print x;
}", "testfile.dfy", CompilationStatus.VerificationSucceeded);
      await Task.Delay(100); // Just time for the diagnostics to be updated
      await AssertHoverMatches(documentItem, (0, 7),
        @"**f** metrics:

No assertion to check."
      );
      await AssertHoverMatches(documentItem, (0, 10),
        "```dafny\nx: int\n```");
    }

    private async Task<TextDocumentItem> GetDocumentItem(string source, string filename, CompilationStatus expectedStatus) {
      source = source.TrimStart();
      var documentItem = CreateTestDocument(source, filename);
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
      var regexExpected = Regex.Escape(expected).Replace(@"\?\?\?", ".*");
      var matched = new Regex(regexExpected).Match(value).Success;
      if (!matched) {
        // A simple helper to determine what portion of the regex did not match
        var helper = "";
        foreach (var chunk in expected.Split("???")) {
          if (!value.Contains(chunk)) {
            helper += $"\nThe result string did not contain '{chunk}'";
          }
        }
        Assert.IsTrue(false, "{0} did not match {1}." + helper, value, regexExpected);
      }
    }

    private async Task<CompilationStatus> WaitUntilDafnyFinishes(TextDocumentItem documentItem) {
      CompilationStatusParams lastResult;
      do {
        lastResult = await notificationReceiver.AwaitNextNotificationAsync(CancellationToken);
        Assert.AreEqual(documentItem.Uri, lastResult.Uri);
        Assert.AreEqual(documentItem.Version, lastResult.Version);
      } while (IsNotDoneYet(lastResult));

      return lastResult.Status;
    }

    private static bool IsNotDoneYet(CompilationStatusParams lastResult) {
      return lastResult.Status != CompilationStatus.VerificationFailed &&
             lastResult.Status != CompilationStatus.VerificationSucceeded &&
             lastResult.Status != CompilationStatus.ParsingFailed &&
             lastResult.Status != CompilationStatus.ResolutionFailed;
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
