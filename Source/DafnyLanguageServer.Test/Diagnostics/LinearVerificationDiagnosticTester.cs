using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.JsonRpc;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Diagnostics;

public abstract class LinearVerificationDiagnosticTester : ClientBasedLanguageServerTest {
  protected TestNotificationReceiver<VerificationDiagnosticsParams> VerificationDiagnosticReceiver;
  [TestInitialize]
  public override async Task SetUp() {
    diagnosticReceiver = new();
    VerificationDiagnosticReceiver = new();
    client = await InitializeClient(options =>
      options
        .OnPublishDiagnostics(diagnosticReceiver.NotificationReceived)
        .AddHandler(DafnyRequestNames.VerificationDiagnostics,
          NotificationHandler.For<VerificationDiagnosticsParams>(VerificationDiagnosticReceiver.NotificationReceived))
      );
  }

  public static Dictionary<LineVerificationStatus, string> LineVerificationStatusToString = new() {
    { LineVerificationStatus.Unknown, "   " },
    { LineVerificationStatus.Scheduled, " s " },
    { LineVerificationStatus.Verifying, " S " },
    { LineVerificationStatus.VerifiedObsolete, " I " },
    { LineVerificationStatus.VerifiedVerifying, " $ " },
    { LineVerificationStatus.Verified, " | " },
    { LineVerificationStatus.ErrorRangeObsolete, "[I]" },
    { LineVerificationStatus.ErrorRangeVerifying, "[S]" },
    { LineVerificationStatus.ErrorRange, "[ ]" },
    { LineVerificationStatus.ErrorObsolete, "[-]" },
    { LineVerificationStatus.ErrorVerifying, "[~]" },
    { LineVerificationStatus.Error, "[=]" },
    { LineVerificationStatus.ErrorRangeAssertionVerifiedObsolete, "[o]" },
    { LineVerificationStatus.ErrorRangeAssertionVerifiedVerifying, "[Q]" },
    { LineVerificationStatus.ErrorRangeAssertionVerified, "[O]" },
    { LineVerificationStatus.ResolutionError, @"/!\" }
  };

  private static bool IsNotIndicatingProgress(LineVerificationStatus status) {
    return status != LineVerificationStatus.Scheduled &&
           status != LineVerificationStatus.Verifying &&
           status != LineVerificationStatus.ErrorObsolete &&
           status != LineVerificationStatus.ErrorVerifying &&
           status != LineVerificationStatus.VerifiedObsolete &&
           status != LineVerificationStatus.VerifiedVerifying &&
           status != LineVerificationStatus.ErrorRangeObsolete &&
           status != LineVerificationStatus.ErrorRangeVerifying;
  }
  public static string RenderTrace(List<LineVerificationStatus[]> statusesTrace, string code) {
    var codeLines = new Regex("\r?\n").Split(code);
    var renderedCode = "";
    for (var line = 0; line < codeLines.Length; line++) {
      if (line != 0) {
        renderedCode += "\n";
      }
      foreach (var statusTrace in statusesTrace) {
        renderedCode += LineVerificationStatusToString[statusTrace[line]];
      }

      renderedCode += ":";
      renderedCode += codeLines[line];
    }

    return renderedCode;
  }

  /// <summary>
  /// Extracts the code from a trace
  /// </summary>
  /// <param name="tracesAndCode"></param>
  /// <returns></returns>
  public static string ExtractCode(string tracesAndCode) {
    var i = 0;
    while (tracesAndCode[i] != ':' && tracesAndCode[i] != '\n') {
      i++;
    }

    if (tracesAndCode[i] == '\n') {
      return tracesAndCode;
    }
    var pattern = $"(?<newline>^|\r?\n).{{{i}}}:(?<line>.*)";
    var regexRemoveTrace = new Regex(pattern);
    var codeWithoutTrace = regexRemoveTrace.Replace(tracesAndCode, match =>
      (match.Groups["newline"].Value == "" ? "" : "\n") + match.Groups["line"].Value
    );
    return codeWithoutTrace;
  }

  protected List<LineVerificationStatus[]> previousTraces = null;

  protected async Task<List<LineVerificationStatus[]>> GetAllLineVerificationDiagnostics(TextDocumentItem documentItem) {
    var traces = new List<LineVerificationStatus[]>();
    var maximumNumberOfTraces = 50;
    var previousPerLineDiagnostics
      = previousTraces == null || previousTraces.Count == 0 ? null :
        previousTraces[^1].ToList();
    var nextDiagnostic = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken);
    for (; maximumNumberOfTraces > 0; maximumNumberOfTraces--) {
      var verificationDiagnosticReport = await VerificationDiagnosticReceiver.AwaitNextNotificationAsync(CancellationToken);
      Assert.AreEqual(documentItem.Uri, verificationDiagnosticReport.Uri);
      var newPerLineDiagnostics = verificationDiagnosticReport.PerLineDiagnostic.ToList();
      if ((previousPerLineDiagnostics != null
          && previousPerLineDiagnostics.SequenceEqual(newPerLineDiagnostics)) ||
          newPerLineDiagnostics.All(status => status == LineVerificationStatus.Unknown)) {
        continue;
      }

      traces.Add(verificationDiagnosticReport.PerLineDiagnostic);
      if (NoMoreNotificationsToAwaitFrom(verificationDiagnosticReport)) {
        break;
      }

      previousPerLineDiagnostics = newPerLineDiagnostics;
    }

    previousTraces = traces;
    return traces;
  }

  private static bool NoMoreNotificationsToAwaitFrom(VerificationDiagnosticsParams verificationDiagnosticReport) {
    return verificationDiagnosticReport.PerLineDiagnostic.Contains(LineVerificationStatus.ResolutionError) ||
           verificationDiagnosticReport.PerLineDiagnostic.All(IsNotIndicatingProgress) ||
           verificationDiagnosticReport.PerLineDiagnostic.All(status => status == LineVerificationStatus.Unknown);
  }

  /// <summary>
  /// Given some code, will emit the edit corresponding to remove the regular expression
  /// .*?//NextN?:
  /// </summary>
  /// <param name="code">The original code with the //Next: comments or //NextN:</param>
  /// <returns></returns>
  public System.Tuple<string, List<System.Tuple<Range, string>>> ExtractCodeAndChanges(string code) {
    var lineMatcher = new Regex(@"\r?\n");
    var matcher = new Regex(@"(?<previousNewline>^|\r?\n)(?<toRemove>.*?//Next(?<id>\d*):)");
    var originalCode = code;
    var matches = matcher.Matches(code);
    var changes = new List<System.Tuple<Range, string>>() { };
    while (matches.Count > 0) {
      var firstChange = 0;
      Match? firstChangeMatch = null;
      for (var i = 0; i < matches.Count; i++) {
        if (matches[i].Groups["id"].Value != "") {
          var intValue = Int32.Parse(matches[i].Groups["id"].Value);
          if (firstChange == 0 || intValue < firstChange) {
            firstChange = intValue;
            firstChangeMatch = matches[i];
          }
        }
      }

      if (firstChangeMatch == null) {
        break;
      }

      var startRemove = firstChangeMatch.Groups["toRemove"].Index;
      var endRemove = startRemove + firstChangeMatch.Groups["toRemove"].Value.Length;

      Position IndexToPosition(int index) {
        var before = code.Substring(0, index);
        var newlines = lineMatcher.Matches(before);
        var line = newlines.Count;
        var character = index;
        if (newlines.Count > 0) {
          var lastNewline = newlines[newlines.Count - 1];
          character = index - (lastNewline.Index + lastNewline.Value.Length);
        }

        return new Position(line, character);
      }

      // For now, simple: Remove the line
      changes.Add(new Tuple<Range, string>(
        new Range(IndexToPosition(startRemove), IndexToPosition(endRemove)), ""));
      code = code.Substring(0, startRemove) + code.Substring(endRemove);
      matches = matcher.Matches(code);
    }

    return new Tuple<string, List<Tuple<Range, string>>>(originalCode, changes);
  }

  public async Task VerifyTrace(string codeAndTrace) {
    codeAndTrace = codeAndTrace.StripMargin();
    var codeAndChanges = ExtractCode(codeAndTrace);
    var (code, changes) = ExtractCodeAndChanges(codeAndChanges);
    var documentItem = CreateTestDocument(code);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var traces = new List<LineVerificationStatus[]>();
    traces.AddRange(await GetAllLineVerificationDiagnostics(documentItem));
    foreach (var (range, inserted) in changes) {
      ApplyChange(ref documentItem, range, inserted);
      traces.AddRange(await GetAllLineVerificationDiagnostics(documentItem));
    }
    var expected = RenderTrace(traces, code);
    AssertWithDiff.Equal(codeAndTrace, expected);

  }
}

public static class StringExtensions {
  public static string StripMargin(this string s) {
    if (!Regex.Match(s, @"(?:^\r?\n?)[ \t]*:").Success) {
      return s;
    }
    return Regex.Replace(s, @"(?:(?<init>^\r?\n?)|(?<newline>\r?\n))[ \t]*:", match =>
      match.Groups["init"].Success ? "" : "\n"
    );
  }
}