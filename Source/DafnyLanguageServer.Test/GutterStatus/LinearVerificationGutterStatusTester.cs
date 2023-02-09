using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.JsonRpc;
using OmniSharp.Extensions.LanguageServer.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Diagnostics;

public abstract class LinearVerificationGutterStatusTester : ClientBasedLanguageServerTest {
  protected TestNotificationReceiver<VerificationStatusGutter> verificationStatusGutterReceiver;

  public override async Task SetUp(Action<DafnyOptions> modifyOptions) {
    verificationStatusGutterReceiver = new();

    void ModifyOptions(DafnyOptions options) {
      options.Set(ServerCommand.LineVerificationStatus, true);
      modifyOptions?.Invoke(options);
    }
    await base.SetUp(ModifyOptions);
  }

  protected override void InitialiseClientHandler(LanguageClientOptions options) {
    base.InitialiseClientHandler(options);
    options
      .AddHandler(DafnyRequestNames.VerificationStatusGutter,
        NotificationHandler.For<VerificationStatusGutter>(verificationStatusGutterReceiver.NotificationReceived));
  }

  public static Dictionary<LineVerificationStatus, string> LineVerificationStatusToString = new() {
    { LineVerificationStatus.Nothing, "   " },
    { LineVerificationStatus.Scheduled, " . " },
    { LineVerificationStatus.Verifying, " S " },
    { LineVerificationStatus.VerifiedObsolete, " I " },
    { LineVerificationStatus.VerifiedVerifying, " $ " },
    { LineVerificationStatus.Verified, " | " },
    { LineVerificationStatus.ErrorContextObsolete, "[I]" },
    { LineVerificationStatus.ErrorContextVerifying, "[S]" },
    { LineVerificationStatus.ErrorContext, "[ ]" },
    { LineVerificationStatus.AssertionFailedObsolete, "[-]" },
    { LineVerificationStatus.AssertionFailedVerifying, "[~]" },
    { LineVerificationStatus.AssertionFailed, "[=]" },
    { LineVerificationStatus.AssertionVerifiedInErrorContextObsolete, "[o]" },
    { LineVerificationStatus.AssertionVerifiedInErrorContextVerifying, "[Q]" },
    { LineVerificationStatus.AssertionVerifiedInErrorContext, "[O]" },
    { LineVerificationStatus.ResolutionError, @"/!\" }
  };

  private static bool IsNotIndicatingProgress(LineVerificationStatus status) {
    return status != LineVerificationStatus.Scheduled &&
           status != LineVerificationStatus.Verifying &&
           status != LineVerificationStatus.AssertionFailedObsolete &&
           status != LineVerificationStatus.AssertionFailedVerifying &&
           status != LineVerificationStatus.VerifiedObsolete &&
           status != LineVerificationStatus.VerifiedVerifying &&
           status != LineVerificationStatus.ErrorContextObsolete &&
           status != LineVerificationStatus.ErrorContextVerifying &&
           status != LineVerificationStatus.AssertionVerifiedInErrorContextObsolete &&
           status != LineVerificationStatus.AssertionVerifiedInErrorContextVerifying;
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
    while (i < tracesAndCode.Length &&
           tracesAndCode[i] != ':' &&
           tracesAndCode[i] != '\n' &&
           (tracesAndCode[i] != '/' || (i + 1 < tracesAndCode.Length && tracesAndCode[i + 1] == '!')) &&
           tracesAndCode[i] != '(') {
      i++;
    }

    // For the first time without trace
    if (i >= tracesAndCode.Length || tracesAndCode[i] != ':') {
      return tracesAndCode;
    }
    var pattern = $"(?<newline>^|\r?\n).{{{i}}}:(?<line>.*)";
    var regexRemoveTrace = new Regex(pattern);
    var codeWithoutTrace = regexRemoveTrace.Replace(tracesAndCode, match =>
      (match.Groups["newline"].Value == "" ? "" : "\n") + match.Groups["line"].Value
    );
    return codeWithoutTrace;
  }

  protected ConcurrentDictionary<TestNotificationReceiver<VerificationStatusGutter>, List<LineVerificationStatus[]>>
    previousTraces = new();

  protected async Task<List<LineVerificationStatus[]>> GetAllLineVerificationStatuses(
      TextDocumentItem documentItem,
      TestNotificationReceiver<VerificationStatusGutter> verificationStatusGutterReceiver
      ) {
    var traces = new List<LineVerificationStatus[]>();
    var maximumNumberOfTraces = 5000;
    var attachedTraces = previousTraces.GetOrCreate(verificationStatusGutterReceiver,
      () => new List<LineVerificationStatus[]>());
    var previousPerLineDiagnostics = !attachedTraces.Any() ? null : attachedTraces[^1].ToList();
    for (; maximumNumberOfTraces > 0; maximumNumberOfTraces--) {
      var verificationStatusGutter = await verificationStatusGutterReceiver.AwaitNextNotificationAsync(CancellationToken);
      if (documentItem.Uri != verificationStatusGutter.Uri || documentItem.Version != verificationStatusGutter.Version) {
        continue;
      }
      var newPerLineDiagnostics = verificationStatusGutter.PerLineStatus.ToList();
      if ((previousPerLineDiagnostics != null
          && previousPerLineDiagnostics.SequenceEqual(newPerLineDiagnostics)) ||
          newPerLineDiagnostics.All(status => status == LineVerificationStatus.Nothing)) {
        continue;
      }

      traces.Add(verificationStatusGutter.PerLineStatus);
      if (NoMoreNotificationsToAwaitFrom(verificationStatusGutter)) {
        break;
      }

      previousPerLineDiagnostics = newPerLineDiagnostics;
    }

    previousTraces.AddOrUpdate(verificationStatusGutterReceiver,
      oldKey => traces,
      (oldKey, _) => traces
      );
    return traces;
  }

  private static bool NoMoreNotificationsToAwaitFrom(VerificationStatusGutter verificationGutterStatus) {
    return verificationGutterStatus.PerLineStatus.Contains(LineVerificationStatus.ResolutionError) ||
           verificationGutterStatus.PerLineStatus.All(IsNotIndicatingProgress) ||
           verificationGutterStatus.PerLineStatus.All(status => status == LineVerificationStatus.Nothing);
  }

  /// <summary>
  /// Given some code, will emit the edit like this:
  /// ```
  /// sentence //Next1:sentence2 //Next2:sentence3
  /// ^^^^^^^^^^^^^^^^^ remove
  /// ```
  /// ```
  /// sentence //Next1:\nsentence2 //Next2:sentence3
  /// ^^^^^^^^^^^^^^^^^^^ replace with newline
  /// ```
  /// ```
  /// sentence //Remove1:sentence2 //Next2:sentence3
  /// ^^^^^^^^^^^^^^^^^^^ remove, including the newline before sentence if any
  /// ```
  /// </summary>
  /// <param name="code">The original code with the //Next: comments or //NextN:</param>
  /// <returns></returns>
  public (string code, List<(Range changeRange, string changeValue)> changes) ExtractCodeAndChanges(string code) {
    var lineMatcher = new Regex(@"\r?\n");
    var matcher = new Regex(@"(?<previousNewline>^|\r?\n)(?<toRemove>.*?//(?<newtOrRemove>Next|Remove)(?<id>\d*):(?<newline>\\n)?)");
    var originalCode = code;
    var matches = matcher.Matches(code);
    var changes = new List<(Range, string)>();
    while (matches.Count > 0) {
      var firstChange = 0;
      Match firstChangeMatch = null;
      for (var i = 0; i < matches.Count; i++) {
        if (matches[i].Groups["id"].Value != "") {
          var intValue = Int32.Parse(matches[i].Groups["id"].Value);
          if (firstChange == 0 || intValue < firstChange) {
            firstChange = intValue;
            firstChangeMatch = matches[i];
          }
        } else {
          firstChangeMatch = matches[i];
          break;
        }
      }

      if (firstChangeMatch == null) {
        break;
      }

      var startRemove =
        firstChangeMatch.Groups["newtOrRemove"].Value == "Next" ?
        firstChangeMatch.Groups["toRemove"].Index :
        firstChangeMatch.Groups["previousNewline"].Index;
      var endRemove = firstChangeMatch.Groups["toRemove"].Index + firstChangeMatch.Groups["toRemove"].Value.Length;

      Position IndexToPosition(int index) {
        var before = code.Substring(0, index);
        var newlines = lineMatcher.Matches(before);
        var line = newlines.Count;
        var character = index;
        if (newlines.Count > 0) {
          var lastNewline = newlines[^1];
          character = index - (lastNewline.Index + lastNewline.Value.Length);
        }

        return new Position(line, character);
      }

      var optionalNewLine = firstChangeMatch.Groups["newline"].Success ? "\n" : "";
      // For now, simple: Remove the line
      changes.Add(new(
        new Range(IndexToPosition(startRemove), IndexToPosition(endRemove)), optionalNewLine));
      code = code.Substring(0, startRemove) + optionalNewLine + code.Substring(endRemove);
      matches = matcher.Matches(code);
    }

    return (originalCode, changes);
  }

  // If testTrace is false, codeAndTree should not contain a trace to test.
  public async Task VerifyTrace(string codeAndTrace, string fileName = null, bool testTrace = true,
    TestNotificationReceiver<VerificationStatusGutter> verificationStatusGutterReceiver = null
    ) {
    if (verificationStatusGutterReceiver == null) {
      verificationStatusGutterReceiver = this.verificationStatusGutterReceiver;
    }
    codeAndTrace = codeAndTrace[0] == '\n' ? codeAndTrace.Substring(1) :
      codeAndTrace.Substring(0, 2) == "\r\n" ? codeAndTrace.Substring(2) :
      codeAndTrace;
    var codeAndChanges = testTrace ? ExtractCode(codeAndTrace) : codeAndTrace;
    var (code, changes) = ExtractCodeAndChanges(codeAndChanges);
    var documentItem = CreateTestDocument(code, fileName);
    client.OpenDocument(documentItem);
    var traces = new List<LineVerificationStatus[]>();
    traces.AddRange(await GetAllLineVerificationStatuses(documentItem, verificationStatusGutterReceiver));
    foreach (var (range, inserted) in changes) {
      ApplyChange(ref documentItem, range, inserted);
      traces.AddRange(await GetAllLineVerificationStatuses(documentItem, verificationStatusGutterReceiver));
    }

    if (testTrace) {
      var traceObtained = RenderTrace(traces, code);
      var ignoreQuestionMarks = AcceptQuestionMarks(traceObtained, codeAndTrace);
      var expected = "\n" + codeAndTrace + "\n";
      var actual = "\n" + ignoreQuestionMarks + "\n";
      AssertWithDiff.Equal(expected, actual);
    }
  }

  // Finds all the "?" at the beginning in expected and replace the characters at the same position in traceObtained
  // by a question mark, so that we don't care what is verified first.
  // Do this only if lengths are the same
  public string AcceptQuestionMarks(string traceObtained, string expected) {
    if (traceObtained.Length != expected.Length) {
      return traceObtained;
    }

    var toFindRegex = new Regex(@"(?<=(?:^|\n)[^:]*)\?");
    var matches = toFindRegex.Matches(expected);
    var pattern = "";
    for (var matchIndex = 0; matchIndex < matches.Count; matchIndex++) {
      pattern += (pattern == "" ? "" : "|")
                 + (@"(?<=^[\S\s]{" + matches[matchIndex].Index + @"}).");
    }

    if (pattern == "") {
      return traceObtained;
    }

    var toReplaceRegex = new Regex(pattern);
    return toReplaceRegex.Replace(traceObtained, "?");
  }
}
