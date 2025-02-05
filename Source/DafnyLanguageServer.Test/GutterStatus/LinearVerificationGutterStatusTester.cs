using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.JsonRpc;
using OmniSharp.Extensions.LanguageServer.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Serilog;
using Xunit.Abstractions;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.GutterStatus;

public abstract class LinearVerificationGutterStatusTester : ClientBasedLanguageServerTest {
  protected TestNotificationReceiver<VerificationStatusGutter> verificationStatusGutterReceiver;

  protected override async Task SetUp(Action<DafnyOptions> modifyOptions) {
    verificationStatusGutterReceiver = new(logger);

    void ModifyOptions(DafnyOptions options) {
      options.Set(GutterIconAndHoverVerificationDetailsManager.LineVerificationStatus, true);
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
  public static string RenderTrace(List<LineVerificationStatus[]> statusesTrace, List<string> codes) {
    var code = codes[0];
    var codeLines = new Regex("\r?\n").Split(code);
    var maxLines = codeLines.Length;
    foreach (var trace in statusesTrace) {
      if (maxLines < trace.Length) {
        maxLines = trace.Length;
      }
    }
    foreach (var intermediateCode in codes) {
      var intermediateCodeLines = new Regex("\r?\n").Split(intermediateCode).Length;
      if (maxLines < intermediateCodeLines) {
        maxLines = intermediateCodeLines;
      }
    }
    var renderedCode = "";
    for (var line = 0; line < maxLines; line++) {
      if (line != 0) {
        renderedCode += "\n";
      }
      foreach (var statusTrace in statusesTrace) {
        if (line >= statusTrace.Length) {
          renderedCode += "###";
        } else {
          renderedCode += NotificationPublisher.LineVerificationStatusToString[statusTrace[line]];
        }
      }

      renderedCode += ":";
      renderedCode += line < codeLines.Length ? codeLines[line] : "";
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

  protected async Task<List<LineVerificationStatus[]>> GetAllLineVerificationStatuses(TextDocumentItem documentItem,
    TestNotificationReceiver<VerificationStatusGutter> verificationStatusGutterReceiver, bool intermediates) {
    var traces = new List<LineVerificationStatus[]>();
    var maximumNumberOfTraces = 5000;
    var attachedTraces = previousTraces.GetOrCreate(verificationStatusGutterReceiver,
      () => []);
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

      if (intermediates) {
        traces.Add(verificationStatusGutter.PerLineStatus);
      }

      if (NoMoreNotificationsToAwaitFrom(verificationStatusGutter)) {
        if (!intermediates) {
          traces.Add(verificationStatusGutter.PerLineStatus);
        }
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
  /// sentence //Replace1:This is a \nsentence2 //Replace2:sentence3 with \\n character
  /// ^^^remove^^^^^^^^^^^          ^^ replace with newline               ^^ replace with \
  /// ```
  /// ```
  /// sentence //Insert1:This is a \nsentence2 //Replace2:sentence3 with \\n character
  ///          ^^^remove^          ^^ replace with newline               ^^ replace with \
  /// ```
  /// ```
  /// sentence //Remove1:sentence2 //Replace2:sentence3
  /// ^^^^^^^^^^^^^^^^^^^ Same as Replace, but will remove also the newline before
  /// ```
  /// </summary>
  /// <param name="code">The original code with the //Replace: comments or //ReplaceN:</param>
  /// <returns></returns>
  public static (string code, List<string> codes, List<List<Change>> changes) ExtractCodeAndChanges(string code) {
    var lineMatcher = new Regex(@"\r?\n");
    var newLineOrDoubleBackslashMatcher = new Regex(@"\\\\|\\n");
    var matcher = new Regex(@"(?<previousNewline>^|\r?\n)(?<toRemove>.*?(?<commentStart>//)(?<keyword>Replace|Remove|Insert)(?<id>\d*):)(?<toInsert>.*)");
    code = code.Trim();
    var codes = new List<string>();
    codes.Add(code);
    var originalCode = code;
    var matches = matcher.Matches(code);
    var changes = new List<List<Change>>();
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

      var keyword = firstChangeMatch.Groups["keyword"].Value;
      var startRemove = keyword switch {
        "Replace" => firstChangeMatch.Groups["toRemove"].Index,
        "Remove" => firstChangeMatch.Groups["previousNewline"].Index,
        "Insert" => firstChangeMatch.Groups["commentStart"].Index,
        _ => throw new Exception("Unexpected keyword: " + keyword + ", expected Replace, Remove or Insert")
      };
      var endRemove = firstChangeMatch.Groups["toRemove"].Index + firstChangeMatch.Groups["toRemove"].Value.Length;

      var toInsert = firstChangeMatch.Groups["toInsert"].Value;
      var toInsertIndex = firstChangeMatch.Groups["toInsert"].Index;
      var allNewlinesOrDoubleBackslashes = newLineOrDoubleBackslashMatcher.Matches(toInsert);


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

      // If there are \n characters in the comments, we replace them by newlines
      // If there are \\ characters in the comments, we replace them by single slashes
      var resultingChange = new List<Change>();
      for (var i = allNewlinesOrDoubleBackslashes.Count - 1; i >= 0; i--) {
        var newlineOrDoubleBackslash = allNewlinesOrDoubleBackslashes[i];
        var isNewline = newlineOrDoubleBackslash.Value == @"\n";
        var index = newlineOrDoubleBackslash.Index;
        var absoluteIndex = toInsertIndex + index;
        var absoluteIndexEnd = absoluteIndex + newlineOrDoubleBackslash.Value.Length;
        var replacement = isNewline ? "\n" : @"\";
        resultingChange.Add(new(
            new Range(IndexToPosition(absoluteIndex), IndexToPosition(absoluteIndexEnd)), replacement
          ));
        code = code.Substring(0, absoluteIndex) + replacement + code.Substring(absoluteIndexEnd);
      }

      resultingChange.Add(new(
        new Range(IndexToPosition(startRemove), IndexToPosition(endRemove)), ""));
      code = code.Substring(0, startRemove) + code.Substring(endRemove);
      matches = matcher.Matches(code);
      changes.Add(resultingChange);
      codes.Add(code);
    }

    return (originalCode, codes, changes);
  }

  // If testTrace is false, codeAndTree should not contain a trace to test.
  public async Task VerifyTrace(string codeAndTrace, bool explicitProject, string fileName = null, bool testTrace = true, bool intermediates = true,
    TestNotificationReceiver<VerificationStatusGutter> verificationStatusGutterReceiver = null) {
    if (verificationStatusGutterReceiver == null) {
      verificationStatusGutterReceiver = this.verificationStatusGutterReceiver;
    }
    codeAndTrace = codeAndTrace[0] == '\n' ? codeAndTrace.Substring(1) :
      codeAndTrace.Substring(0, 2) == "\r\n" ? codeAndTrace.Substring(2) :
      codeAndTrace;
    var codeAndChanges = testTrace ? ExtractCode(codeAndTrace) : codeAndTrace;
    var (code, codes, changesList) = ExtractCodeAndChanges(codeAndChanges);

    var documentItem = CreateTestDocument(code.Trim(), fileName, 1);
    if (explicitProject) {
      await CreateOpenAndWaitForResolve("", Path.Combine(Path.GetDirectoryName(documentItem.Uri.GetFileSystemPath())!, DafnyProject.FileName));
    }
    client.OpenDocument(documentItem);
    var traces = new List<LineVerificationStatus[]>();
    traces.AddRange(await GetAllLineVerificationStatuses(documentItem, verificationStatusGutterReceiver, intermediates: intermediates));
    foreach (var changes in changesList) {
      ApplyChanges(ref documentItem, changes);
      traces.AddRange(await GetAllLineVerificationStatuses(documentItem, verificationStatusGutterReceiver, intermediates: intermediates));
    }

    if (testTrace) {
      var traceObtained = RenderTrace(traces, codes);
      var ignoreQuestionMarks = AcceptQuestionMarks(traceObtained, codeAndTrace);
      var expected = "\n" + codeAndTrace + "\n";
      var actual = "\n" + ignoreQuestionMarks + "\n";
      AssertWithDiff.Equal(expected, actual, fileName);
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

  protected LinearVerificationGutterStatusTester(ITestOutputHelper output) : base(output) {
    ProjectManager.GutterIconTesting = true;
    Disposable.Add(System.Reactive.Disposables.Disposable.Create(() => ProjectManager.GutterIconTesting = false));
  }
}
