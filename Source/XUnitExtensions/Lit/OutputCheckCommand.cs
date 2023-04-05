using System;
using System.Collections;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using CommandLine;
using Xunit.Abstractions;

namespace XUnitExtensions.Lit {
  public class OutputCheckOptions {

    [Value(0)]
    public string? CheckFile { get; set; } = default!;

    [Option("file-to-check", Required = true, HelpText = "File to check")]
    public string? FileToCheck { get; set; } = default!;
  }

  public readonly record struct OutputCheckCommand(OutputCheckOptions options) : ILitCommand {

    private abstract record CheckDirective(string File, int LineNumber) {

      private static readonly Dictionary<string, Func<string, int, string, CheckDirective>> DirectiveParsers = new();
      static CheckDirective() {
        DirectiveParsers.Add("CHECK:", CheckRegexp.Parse);
        DirectiveParsers.Add("CHECK-L:", CheckLiteral.Parse);
        DirectiveParsers.Add("CHECK-NEXT:", CheckNextRegexp.Parse);
        DirectiveParsers.Add("CHECK-NEXT-L:", CheckNextLiteral.Parse);
        DirectiveParsers.Add("CHECK-NOT:", CheckNotRegexp.Parse);
        DirectiveParsers.Add("CHECK-NOT-L:", CheckNotLiteral.Parse);
      }

      public static CheckDirective? Parse(string file, int lineNumber, string line) {
        foreach (var (keyword, parser) in DirectiveParsers) {
          var index = line.IndexOf(keyword);
          if (index >= 0) {
            var arguments = line[(index + keyword.Length)..].Trim();
            return parser(file, lineNumber, arguments);
          }
        }
        return null;
      }

      public abstract bool FindMatch(IEnumerator<string> lines);
    }

    private record CheckRegexp(string File, int LineNumber, Regex Pattern) : CheckDirective(File, LineNumber) {
      public new static CheckDirective Parse(string file, int lineNumber, string arguments) {
        return new CheckRegexp(file, lineNumber, new Regex(arguments));
      }

      public override bool FindMatch(IEnumerator<string> lines) {
        while (lines.MoveNext()) {
          if (Pattern.IsMatch(lines.Current)) {
            return true;
          }
        }
        return false;
      }

      public override string ToString() {
        return $"Check Directive ({File}:{LineNumber} Pattern: '{Pattern}')";
      }
    }

    private record CheckNextRegexp(string File, int LineNumber, Regex Pattern) : CheckDirective(File, LineNumber) {
      public new static CheckDirective Parse(string file, int lineNumber, string arguments) {
        return new CheckNextRegexp(file, lineNumber, new Regex(arguments));
      }

      public override bool FindMatch(IEnumerator<string> lines) {
        if (!lines.MoveNext()) {
          throw new Exception("No more lines to match against");
        }

        return Pattern.IsMatch(lines.Current);
      }

      public override string ToString() {
        return $"CheckNext Directive ({File}:{LineNumber} Pattern: '{Pattern}')";
      }
    }

    private record CheckLiteral(string File, int LineNumber, string Literal) : CheckDirective(File, LineNumber) {
      public new static CheckDirective Parse(string file, int lineNumber, string arguments) {
        return new CheckLiteral(file, lineNumber, arguments);
      }

      public override bool FindMatch(IEnumerator<string> lines) {
        while (lines.MoveNext()) {
          if (Literal == lines.Current.Trim()) {
            return true;
          }
        }
        return false;
      }

      public override string ToString() {
        return $"CheckLiteral Directive ({File}:{LineNumber} Literal: '{Literal}')";
      }
    }

    private record CheckNextLiteral(string File, int LineNumber, string Literal) : CheckDirective(File, LineNumber) {
      public new static CheckDirective Parse(string file, int lineNumber, string arguments) {
        return new CheckNextLiteral(file, lineNumber, arguments);
      }

      public override bool FindMatch(IEnumerator<string> lines) {
        if (!lines.MoveNext()) {
          throw new Exception("No more lines to match against");
        }

        return Literal == lines.Current.Trim();
      }

      public override string ToString() {
        return $"CheckNextLiteral Directive ({File}:{LineNumber} Literal: '{Literal}')";
      }
    }

    private class CheckingEnumerator : IEnumerator<string> {
      private readonly IEnumerator<string> Wrapped;
      private readonly Action<string> Check;

      public CheckingEnumerator(IEnumerator<string> wrapped, Action<string> check) {
        Wrapped = wrapped;
        Check = check;
      }

      public bool MoveNext() {
        var result = Wrapped.MoveNext();
        if (result) {
          Check.Invoke(Wrapped.Current);
        }
        return result;
      }

      public void Reset() {
        throw new NotImplementedException();
      }

      object IEnumerator.Current => Current;

      public string Current => Wrapped.Current;

      public void Dispose() => Wrapped.Dispose();
    }

    private record CheckNotRegexp(string File, int LineNumber, Regex Pattern) : CheckDirective(File, LineNumber) {
      public new static CheckDirective Parse(string file, int lineNumber, string arguments) {
        return new CheckNotRegexp(file, lineNumber, new Regex(arguments));
      }

      public override bool FindMatch(IEnumerator<string> lines) {
        // This directive is tested using a CheckingEnumerator instead.
        throw new NotImplementedException();
      }

      public override string ToString() {
        return $"CheckNot Directive ({File}:{LineNumber} Pattern: '{Pattern}')";
      }
    }

    private record CheckNotLiteral(string File, int LineNumber, string Literal) : CheckDirective(File, LineNumber) {
      public new static CheckDirective Parse(string file, int lineNumber, string arguments) {
        return new CheckNotLiteral(file, lineNumber, arguments);
      }

      public override bool FindMatch(IEnumerator<string> lines) {
        // This directive is tested using a CheckingEnumerator instead.
        throw new NotImplementedException();
      }

      public override string ToString() {
        return $"CheckNotLiteral Directive ({File}:{LineNumber} Literal: '{Literal}')";
      }
    }

    public static ILitCommand Parse(IEnumerable<string> args, LitTestConfiguration config) {
      ILitCommand? result = null;
      Parser.Default.ParseArguments<OutputCheckOptions>(args).WithParsed(o => {
        result = new OutputCheckCommand(o);
      });
      return result!;
    }

    public (int, string, string) Execute(TextReader inputReader,
      TextWriter outputWriter, TextWriter errorWriter) {
      if (options.FileToCheck == null) {
        return (0, "", "");
      }

      var linesToCheck = File.ReadAllLines(options.FileToCheck).ToList();
      var fileName = options.CheckFile;
      if (fileName == null) {
        return (0, "", "");
      }

      var checkDirectives = File.ReadAllLines(options.CheckFile!)
        .Select((line, index) => CheckDirective.Parse(fileName, index + 1, line))
        .Where(e => e != null).Cast<CheckDirective>()
        .Select(e => e!)
        .ToList();
      if (!checkDirectives.Any()) {
        return (1, "", $"ERROR: '{fileName}' does not contain any CHECK directives");
      }

      IEnumerator<string> lineEnumerator = linesToCheck.GetEnumerator();
      IEnumerator<string>? notCheckingEnumerator = null;
      foreach (var directive in checkDirectives) {
        // CHECK-NOT[-L] directives apply up until the next directive, so we handle
        // them by wrapping the line enumerator for the next time through the loop.
        if (directive is CheckNotRegexp(var _, var _, var pattern)) {
          notCheckingEnumerator = new CheckingEnumerator(lineEnumerator, line => {
            if (pattern.IsMatch(line)) {
              throw new Exception($"Match found for {directive}: {line}");
            };
          });
        } else if (directive is CheckNotLiteral(var _, var _, var literal)) {
          notCheckingEnumerator = new CheckingEnumerator(lineEnumerator, line => {
            if (literal == line.Trim()) {
              throw new Exception($"Match found for {directive}: {line}");
            };
          });
        } else {
          var enumerator = notCheckingEnumerator ?? lineEnumerator;
          if (!directive.FindMatch(enumerator)) {
            return (1, "", $"ERROR: Could not find a match for {directive}");
          }
          notCheckingEnumerator = null;
        }
      }
      if (notCheckingEnumerator != null) {
        // Traverse the rest of the enumerator to make sure the CHECK-NOT[-L] directive is fully tested.
        while (notCheckingEnumerator.MoveNext()) { }
      }

      return (0, "", "");
    }

    public override string ToString() {
      return $"OutputCheck --file-to-check {options.FileToCheck} {options.CheckFile}";
    }
  }
}
