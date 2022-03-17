using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Diagnostics;

[TestClass]
public class SimpleLinearVerificationDiagnosticTester : LinearVerificationDiagnosticTester {
  private const int MaxTestExecutionTimeMs = 10000;

  [TestInitialize]
  public override Task SetUp() => base.SetUp();

  /// <summary>
  /// Given some code, will emit the edit corresponding to remove the regular expression
  /// .*?//NextN?:
  /// </summary>
  /// <param name="code">The original code with the //Next: comments or //NextN:</param>
  /// <returns></returns>
  public Tuple<string, List<Tuple<Range, string>>> ExtractCodeAndChanges(string code) {
    var lineMatcher = new Regex(@"\r?\n");
    var matcher = new Regex(@"(?<previousNewline>^|\r?\n)(?<toRemove>.*?//Next(?<id>\d*):)");
    var originalCode = code;
    var matches = matcher.Matches(code);
    var changes = new List<Tuple<Range, string>>() { };
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

  [TestMethod/*, Timeout(MaxTestExecutionTimeMs)*/]
  public async Task EnsureVerificationDiagnosticsAreWorking() {
    var codeAndTrace = @"
    : s  |  |  |  I  I  |  | :predicate Ok() {
    : s  |  |  |  I  I  |  | :  true
    : s  |  |  |  I  I  |  | :}
    :    |  |  |  I  I  |  | :
    : s  S [S][ ][I][I][S] | :method Test(x: bool) returns (i: int)
    : s  S [=][=][-][-][~] | :   ensures i == 2
    : s  S [S][ ][I][I][S] | :{
    : s  S [S][ ][I][I][S] | :  if x {
    : s  S [S][ ][I][I][S] | :    i := 2;
    : s  S [=][=][-][-][~] | :  } else {
    : s  S [S][ ]/!\[I][S] | :    i := 1; //Next1:   i := /; //Next2:    i := 2;
    : s  S [S][ ][I][I][S] | :  }
    : s  S [S][ ][I][I][S] | :}
    :    |  |  |  I  I  |  | :    
    : s  |  |  |  I  I  |  | :predicate OkBis() {
    : s  |  |  |  I  I  |  | :  false
    : s  |  |  |  I  I  |  | :}".StripMargin();
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