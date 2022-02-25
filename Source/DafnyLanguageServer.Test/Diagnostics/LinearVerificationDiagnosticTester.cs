using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.JsonRpc;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

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
    { LineVerificationStatus.Unknown, " ? " },
    { LineVerificationStatus.Scheduled, " s " },
    { LineVerificationStatus.Verifying, " S " },
    { LineVerificationStatus.VerifiedObsolete, " v " },
    { LineVerificationStatus.VerifiedVerifying, " V " },
    { LineVerificationStatus.Verified, " | " },
    { LineVerificationStatus.ErrorRangeObsolete, "|s|" },
    { LineVerificationStatus.ErrorRangeVerifying, "|S|" },
    { LineVerificationStatus.ErrorRange, "| |" },
    { LineVerificationStatus.ErrorObsolete, "|-|" },
    { LineVerificationStatus.ErrorVerifying, "|~|" },
    { LineVerificationStatus.Error, "|=|" },
    { LineVerificationStatus.ResolutionError, @"/!\" }
  };

  protected static bool IsNotIndicatingProgress(LineVerificationStatus status) {
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
    while (tracesAndCode[i] != ':') {
      i++;
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
}

public static class StringExtensions {
  public static string StripMargin(this string s) {
    return Regex.Replace(s, @"(?:(?<init>^\r?\n?)|(?<newline>\r?\n))[ \t]+:", match =>
      match.Groups["init"].Success ? "" : "\n"
    );
  }
}