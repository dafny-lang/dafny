using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.CommandLine;
using System.IO;
using System.Linq;
using System.Runtime.CompilerServices;
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

  private static readonly ConditionalWeakTable<DafnyOptions, ConcurrentDictionary<Uri, List<string>>> fsCaches = new();

  private DafnyOptions options;

  public record ImplementationLogEntry(string Name, Boogie.IToken Tok);
  public record VCResultLogEntry(
    int VCNum,
    DateTime StartTime,
    TimeSpan RunTime,
    SolverOutcome Outcome,
    List<(Boogie.IToken Tok, string Description)> Asserts,
    IEnumerable<TrackedNodeComponent> CoveredElements,
    int ResourceCount);
  public record VerificationResultLogEntry(
    VcOutcome Outcome,
    TimeSpan RunTime,
    int ResourceCount,
    List<VCResultLogEntry> VCResults,
    List<Counterexample> Counterexamples);
  public record ConsoleLogEntry(ImplementationLogEntry Implementation, VerificationResultLogEntry Result);

  public static VerificationResultLogEntry DistillVerificationResult(ImplementationRunResult verificationResult) {
    return new VerificationResultLogEntry(
      verificationResult.VcOutcome, verificationResult.End - verificationResult.Start,
      verificationResult.ResourceCount, verificationResult.RunResults.Select(DistillVCResult).ToList(), verificationResult.Errors);
  }

  private static VCResultLogEntry DistillVCResult(VerificationRunResult r) {
    return new VCResultLogEntry(r.VcNum, r.StartTime, r.RunTime, r.Outcome,
        r.Asserts.Select(a => (a.tok, a.Description.SuccessDescription)).ToList(), r.CoveredElements,
        r.ResourceCount);
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

  private static string GetFileLine(DafnyOptions options, Uri uri, int lineIndex) {
    var fsCache = fsCaches.GetOrCreateValue(options)!;
    List<string> lines = fsCache.GetOrAdd(uri, key => {
      try {
        // Note: This is not guaranteed to be the same file that Dafny parsed. To ensure that, Dafny should keep
        // an in-memory version of each file it parses.
        var file = DafnyFile.CreateAndValidate(new ErrorReporterSink(options), OnDiskFileSystem.Instance, options, uri, Token.NoToken);
        using var reader = file.GetContent();
        lines = Util.Lines(reader).ToList();
      } catch (Exception) {
        lines = new List<string>();
      }
      return lines;
    });
    if (0 <= lineIndex && lineIndex < lines.Count) {
      return lines[lineIndex];
    }
    return null;
  }

  public static void WriteSourceCodeSnippet(DafnyOptions options, IToken tok, TextWriter tw) {
    string line = GetFileLine(options, tok.Uri, tok.line - 1);
    if (line == null) {
      return;
    }

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
        WriteSourceCodeSnippet(Options, dafnyTok, tw);
      } else {
        ErrorWriteLine(tw, "No Dafny location information, so snippet can't be generated.");
      }
    }

    if (tok is NestedToken nestedToken) {
      ReportBplError(nestedToken.Inner, "Related location", false, tw);
    }
  }

  public override void ReportEndVerifyImplementation(Implementation implementation, ImplementationRunResult result) {
    var impl = new ImplementationLogEntry(implementation.VerboseName, implementation.tok);
    VerificationResults.Add(new ConsoleLogEntry(impl, DistillVerificationResult(result)));
  }
}