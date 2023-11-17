using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.CommandLine;
using System.IO;
using System.Linq;
using DafnyCore;
using Microsoft.Boogie;
using VC;

namespace Microsoft.Dafny;

public class DafnyConsolePrinter : ConsolePrinter {
  public new DafnyOptions Options {
    get => options;
    set {
      base.Options = value;
      options = value;
    }
  }

  private readonly ConcurrentDictionary<Uri, List<string>> fsCache = new();
  private DafnyOptions options;

  public record ImplementationLogEntry(string Name, Boogie.IToken Tok);
  public record VCResultLogEntry(
    int VCNum,
    DateTime StartTime,
    TimeSpan RunTime,
    ProverInterface.Outcome Outcome,
    List<(Boogie.IToken Tok, string Description)> Asserts,
    IEnumerable<TrackedNodeComponent> CoveredElements,
    int ResourceCount);
  public record VerificationResultLogEntry(
    ConditionGeneration.Outcome Outcome,
    TimeSpan RunTime,
    int ResourceCount,
    List<VCResultLogEntry> VCResults);
  public record ConsoleLogEntry(ImplementationLogEntry Implementation, VerificationResultLogEntry Result);

  public static VerificationResultLogEntry DistillVerificationResult(VerificationResult verificationResult) {
    return new VerificationResultLogEntry(
      verificationResult.Outcome, verificationResult.End - verificationResult.Start,
      verificationResult.ResourceCount, verificationResult.VCResults.Select(DistillVCResult).ToList());
  }

  private static VCResultLogEntry DistillVCResult(VCResult r) {
    return new VCResultLogEntry(r.vcNum, r.startTime, r.runTime, r.outcome,
        r.asserts.Select(a => (a.tok, a.Description.SuccessDescription)).ToList(), r.coveredElements,
        r.resourceCount);
  }

  public ConcurrentBag<ConsoleLogEntry> VerificationResults { get; } = new();

  public override void AdvisoryWriteLine(TextWriter output, string format, params object[] args) {
    if (output == Console.Out) {
      int foregroundColor = (int)Console.ForegroundColor;
      Console.ForegroundColor = ConsoleColor.Yellow;
      output.WriteLine(format, args);
      Console.ForegroundColor = (ConsoleColor)foregroundColor;
    } else {
      output.WriteLine(format, args);
    }
  }

  private string GetFileLine(Uri uri, int lineIndex) {
    List<string> lines = fsCache.GetOrAdd(uri, key => {
      try {
        // Note: This is not guaranteed to be the same file that Dafny parsed. To ensure that, Dafny should keep
        // an in-memory version of each file it parses.
        var file = DafnyFile.CreateAndValidate(new ErrorReporterSink(options), OnDiskFileSystem.Instance, options, uri, Token.NoToken);
        var reader = file.GetContent();
        lines = Util.Lines(reader).ToList();
      } catch (Exception) {
        lines = new List<string>();
      }
      return lines;
    });
    if (0 <= lineIndex && lineIndex < lines.Count) {
      return lines[lineIndex];
    }
    return "<nonexistent line>";
  }

  public void WriteSourceCodeSnippet(IToken tok, TextWriter tw) {
    string line = GetFileLine(tok.Uri, tok.line - 1);
    string lineNumber = tok.line.ToString();
    string lineNumberSpaces = new string(' ', lineNumber.Length);
    string columnSpaces = new string(' ', tok.col - 1);
    var lineStartPos = tok.pos - tok.col + 1;
    var lineEndPos = lineStartPos + line.Length;

    var tokEndPos = tok.pos + tok.val.Length;
    if (tok is RangeToken rangeToken) {
      tokEndPos = rangeToken.EndToken.pos + rangeToken.EndToken.val.Length;
    }
    var underlineLength = Math.Max(1, Math.Min(tokEndPos - tok.pos, lineEndPos - tok.pos));
    string underline = new string('^', underlineLength);
    tw.WriteLine($"{lineNumberSpaces} |");
    tw.WriteLine($"{lineNumber} | {line}");
    tw.WriteLine($"{lineNumberSpaces} | {columnSpaces}{underline}");
    tw.WriteLine("");
  }

  public static readonly Option<bool> ShowSnippets = new("--show-snippets", () => true,
    "Show a source code snippet for each Dafny message.");

  static DafnyConsolePrinter() {
    DooFile.RegisterNoChecksNeeded(ShowSnippets);
  }

  public DafnyConsolePrinter(DafnyOptions options) {
    Options = options;
  }

  public override void ReportBplError(Boogie.IToken tok, string message, bool error, TextWriter tw, string category = null) {

    if (Options.Verbosity == CoreOptions.VerbosityLevel.Silent) {
      return;
    }

    if (category != null) {
      message = $"{category}: {message}";
    }

    var dafnyToken = BoogieGenerator.ToDafnyToken(options.Get(ShowSnippets), tok);
    message = $"{dafnyToken.TokenToString(Options)}: {message}";

    if (error) {
      ErrorWriteLine(tw, message);
    } else {
      tw.WriteLine(message);
    }

    if (Options.Get(ShowSnippets)) {
      if (tok is IToken dafnyTok) {
        WriteSourceCodeSnippet(dafnyTok, tw);
      } else {
        ErrorWriteLine(tw, "No Dafny location information, so snippet can't be generated.");
      }
    }

    if (tok is NestedToken nestedToken) {
      ReportBplError(nestedToken.Inner, "Related location", false, tw);
    }
  }

  public override void ReportEndVerifyImplementation(Implementation implementation, VerificationResult result) {
    var impl = new ImplementationLogEntry(implementation.VerboseName, implementation.tok);
    VerificationResults.Add(new ConsoleLogEntry(impl, DistillVerificationResult(result)));
  }
}
